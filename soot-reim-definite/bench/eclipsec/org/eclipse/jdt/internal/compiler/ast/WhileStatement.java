/*******************************************************************************
 * Copyright (c) 2000, 2004 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/
package org.eclipse.jdt.internal.compiler.ast;
//import checkers.inference.ownership.quals.*;

import org.eclipse.jdt.internal.compiler.ASTVisitor;
import org.eclipse.jdt.internal.compiler.impl.*;
import org.eclipse.jdt.internal.compiler.classfmt.ClassFileConstants;
import org.eclipse.jdt.internal.compiler.codegen.*;
import org.eclipse.jdt.internal.compiler.flow.*;
import org.eclipse.jdt.internal.compiler.lookup.*;

public class WhileStatement extends Statement {
	
	public Expression condition;
	public Statement action;
	private Label breakLabel, continueLabel;
	int preCondInitStateIndex = -1;
	int condIfTrueInitStateIndex = -1;
	int mergedInitStateIndex = -1;

	public WhileStatement(Expression condition, /*@OwnOwn*/ Statement action, int s, int e) {

		this.condition = condition;
		this.action = action;
		// remember useful empty statement
		if (action instanceof EmptyStatement) action.bits |= IsUsefulEmptyStatement;
		sourceStart = s;
		sourceEnd = e;
	}

	public FlowInfo analyseCode(
		BlockScope currentScope,
		FlowContext flowContext,
		FlowInfo flowInfo) {

		breakLabel = new Label();
		continueLabel = new Label(); 

		Constant cst = this.condition.constant;
		boolean isConditionTrue = cst != Constant.NotAConstant && cst.booleanValue() == true;
		boolean isConditionFalse = cst != Constant.NotAConstant && cst.booleanValue() == false;

		cst = this.condition.optimizedBooleanConstant();
		boolean isConditionOptimizedTrue = cst != Constant.NotAConstant && cst.booleanValue() == true;
		boolean isConditionOptimizedFalse = cst != Constant.NotAConstant && cst.booleanValue() == false;
		
		preCondInitStateIndex =
			currentScope.methodScope().recordInitializationStates(flowInfo);
		LoopingFlowContext condLoopContext;
		FlowInfo condInfo = flowInfo.copy().unconditionalInits().discardNullRelatedInitializations();
		condInfo = this.condition.analyseCode(
				currentScope,
				(condLoopContext =
					new LoopingFlowContext(flowContext, (/*@OwnPar*/ /*@NoRep*/ WhileStatement)this, null, null, currentScope)),
				condInfo);

		LoopingFlowContext loopingContext;
		FlowInfo actionInfo;
		FlowInfo exitBranch;
		if (action == null 
			|| (action.isEmptyBlock() && currentScope.compilerOptions().complianceLevel <= ClassFileConstants.JDK1_3)) {
			condLoopContext.complainOnDeferredChecks(currentScope, condInfo);
			if (isConditionTrue) {
				return FlowInfo.DEAD_END;
			} else {
				FlowInfo mergedInfo = condInfo.initsWhenFalse().unconditionalInits();
				if (isConditionOptimizedTrue){
					mergedInfo.setReachMode(FlowInfo.UNREACHABLE);
				}
				mergedInitStateIndex =
					currentScope.methodScope().recordInitializationStates(mergedInfo);
				return mergedInfo;
			}
		} else {
			// in case the condition was inlined to false, record the fact that there is no way to reach any 
			// statement inside the looping action
			loopingContext =
				new LoopingFlowContext(
					flowContext,
					(/*@OwnPar*/ /*@NoRep*/ WhileStatement)this,
					breakLabel,
					continueLabel,
					currentScope);
			if (isConditionFalse) {
				actionInfo = FlowInfo.DEAD_END;
			} else {
				actionInfo = condInfo.initsWhenTrue().copy();
				if (isConditionOptimizedFalse){
					actionInfo.setReachMode(FlowInfo.UNREACHABLE);
				}
			}

			// for computing local var attributes
			condIfTrueInitStateIndex =
				currentScope.methodScope().recordInitializationStates(
					condInfo.initsWhenTrue());

			if (!this.action.complainIfUnreachable(actionInfo, currentScope, false)) {
				actionInfo = this.action.analyseCode(currentScope, loopingContext, actionInfo);
			}

			// code generation can be optimized when no need to continue in the loop
			exitBranch = condInfo.initsWhenFalse();
			exitBranch.addInitializationsFrom(flowInfo); // recover null inits from before condition analysis
			if (!actionInfo.isReachable() && !loopingContext.initsOnContinue.isReachable()) {
				continueLabel = null;
			} else {
				condLoopContext.complainOnDeferredChecks(currentScope, condInfo);
				actionInfo = actionInfo.mergedWith(loopingContext.initsOnContinue.unconditionalInits());
				loopingContext.complainOnDeferredChecks(currentScope, actionInfo);
				exitBranch.addPotentialInitializationsFrom(actionInfo.unconditionalInits());
			}
		}

		// end of loop
		FlowInfo mergedInfo = FlowInfo.mergedOptimizedBranches(
				loopingContext.initsOnBreak, 
				isConditionOptimizedTrue, 
				exitBranch,
				isConditionOptimizedFalse,
				!isConditionTrue /*while(true); unreachable(); */);
		mergedInitStateIndex = currentScope.methodScope().recordInitializationStates(mergedInfo);
		return mergedInfo;
	}

	/**
	 * While code generation
	 *
	 * @param currentScope org.eclipse.jdt.internal.compiler.lookup.BlockScope
	 * @param codeStream org.eclipse.jdt.internal.compiler.codegen.CodeStream
	 */
	public void generateCode(BlockScope currentScope, CodeStream codeStream) {

		if ((bits & IsReachable) == 0) {
			return;
		}
		int pc = codeStream.position;
		Constant cst = this.condition.optimizedBooleanConstant();
		boolean isConditionOptimizedFalse = cst != Constant.NotAConstant && cst.booleanValue() == false;
		if (isConditionOptimizedFalse) {
			condition.generateCode(currentScope, 	codeStream, false);
			// May loose some local variable initializations : affecting the local variable attributes
			if (mergedInitStateIndex != -1) {
				codeStream.removeNotDefinitelyAssignedVariables(currentScope, mergedInitStateIndex);
				codeStream.addDefinitelyAssignedVariables(currentScope, mergedInitStateIndex);
			}
			codeStream.recordPositionsFrom(pc, this.sourceStart);
			return;
		}
		
		breakLabel.initialize(codeStream);

		// generate condition
		if (continueLabel == null) {
			// no need to reverse condition
			if (condition.constant == Constant.NotAConstant) {
				condition.generateOptimizedBoolean(
					currentScope,
					codeStream,
					null,
					breakLabel,
					true);
			}
		} else {
			continueLabel.initialize(codeStream);
			if (!(((condition.constant != Constant.NotAConstant)
				&& (condition.constant.booleanValue() == true))
				|| (action == null)
				|| action.isEmptyBlock())) {
				int jumpPC = codeStream.position;
				codeStream.goto_(continueLabel);
				codeStream.recordPositionsFrom(jumpPC, condition.sourceStart);
			}
		}
		// generate the action
		Label actionLabel;
		(actionLabel = new Label(codeStream)).place();
		if (action != null) {
			// Required to fix 1PR0XVS: LFRE:WINNT - Compiler: variable table for method appears incorrect
			if (condIfTrueInitStateIndex != -1) {
				// insert all locals initialized inside the condition into the action generated prior to the condition
				codeStream.addDefinitelyAssignedVariables(
					currentScope,
					condIfTrueInitStateIndex);
			}
			action.generateCode(currentScope, codeStream);
			// May loose some local variable initializations : affecting the local variable attributes
			if (preCondInitStateIndex != -1) {
				codeStream.removeNotDefinitelyAssignedVariables(currentScope, preCondInitStateIndex);
			}

		}
		// output condition and branch back to the beginning of the repeated action
		if (continueLabel != null) {
			continueLabel.place();
			condition.generateOptimizedBoolean(
				currentScope,
				codeStream,
				actionLabel,
				null,
				true);
		}
		breakLabel.place();

		// May loose some local variable initializations : affecting the local variable attributes
		if (mergedInitStateIndex != -1) {
			codeStream.removeNotDefinitelyAssignedVariables(currentScope, mergedInitStateIndex);
			codeStream.addDefinitelyAssignedVariables(currentScope, mergedInitStateIndex);
		}
		codeStream.recordPositionsFrom(pc, this.sourceStart);
	}

	public void resolve(BlockScope scope) {

		TypeBinding type = condition.resolveTypeExpecting(scope, BooleanBinding);
		condition.computeConversion(scope, type, type);
		if (action != null)
			action.resolve(scope);
	}

	public StringBuffer printStatement(int tab, StringBuffer output) {

		printIndent(tab, output).append("while ("); //$NON-NLS-1$
		condition.printExpression(0, output).append(')');
		if (action == null)
			output.append(';');
		else
			action.printStatement(tab + 1, output); 
		return output;
	}

	public void traverse(
		ASTVisitor visitor,
		BlockScope blockScope) {

		if (visitor.visit((/*@OwnPar*/ /*@NoRep*/ WhileStatement)this, blockScope)) {
			condition.traverse(visitor, blockScope);
			if (action != null)
				action.traverse(visitor, blockScope);
		}
		visitor.endVisit((/*@OwnPar*/ /*@NoRep*/ WhileStatement)this, blockScope);
	}
}
