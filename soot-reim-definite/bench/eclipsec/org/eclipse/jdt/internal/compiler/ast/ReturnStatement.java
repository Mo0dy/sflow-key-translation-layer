/*******************************************************************************
 * Copyright (c) 2000, 2005 IBM Corporation and others.
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
import org.eclipse.jdt.internal.compiler.codegen.*;
import org.eclipse.jdt.internal.compiler.flow.*;
import org.eclipse.jdt.internal.compiler.impl.Constant;
import org.eclipse.jdt.internal.compiler.lookup.*;

public class ReturnStatement extends Statement {
		
	public Expression expression;
	public boolean isSynchronized;
	public SubRoutineStatement[] subroutines;
	public boolean isAnySubRoutineEscaping = false;
	public LocalVariableBinding saveValueVariable;
	
	public ReturnStatement(Expression expression, int sourceStart, int sourceEnd) {
		this.sourceStart = sourceStart;
		this.sourceEnd = sourceEnd;
		this.expression = expression ;
	}
	public FlowInfo analyseCode(BlockScope currentScope, FlowContext flowContext, FlowInfo flowInfo) {	// here requires to generate a sequence of finally blocks invocations depending corresponding
		// to each of the traversed try statements, so that execution will terminate properly.
	
		// lookup the label, this should answer the returnContext
	
		if (this.expression != null) {
			flowInfo = this.expression.analyseCode(currentScope, flowContext, flowInfo);
		}
		// compute the return sequence (running the finally blocks)
		FlowContext traversedContext = flowContext;
		int subIndex = 0, maxSub = 5;
		boolean saveValueNeeded = false;
		boolean hasValueToSave = this.expression != null && this.expression.constant == Constant.NotAConstant;
		do {
			SubRoutineStatement sub;
			if ((sub = traversedContext.subRoutine()) != null) {
				if (this.subroutines == null){
					this.subroutines = new SubRoutineStatement[maxSub];
				}
				if (subIndex == maxSub) {
					System.arraycopy(this.subroutines, 0, (this.subroutines = new SubRoutineStatement[maxSub *= 2]), 0, subIndex); // grow
				}
				this.subroutines[subIndex++] = sub;
				if (sub.isSubRoutineEscaping()) {
					saveValueNeeded = false;
					isAnySubRoutineEscaping = true;
					break;
				}
			}
			traversedContext.recordReturnFrom(flowInfo.unconditionalInits());
	
			ASTNode node;
			if ((node = traversedContext.associatedNode) instanceof SynchronizedStatement) {
				isSynchronized = true;
	
			} else if (node instanceof TryStatement) {
				TryStatement tryStatement = (TryStatement) node;
				flowInfo.addInitializationsFrom(tryStatement.subRoutineInits); // collect inits
				if (hasValueToSave) {
					if (this.saveValueVariable == null){ // closest subroutine secret variable is used
						prepareSaveValueLocation(tryStatement);
					}
					saveValueNeeded = true;
				}
	
			} else if (traversedContext instanceof InitializationFlowContext) {
					currentScope.problemReporter().cannotReturnInInitializer((/*@OwnPar*/ /*@NoRep*/ ReturnStatement)this);
					return FlowInfo.DEAD_END;
			}
		} while ((traversedContext = traversedContext.parent) != null);
		
		// resize subroutines
		if ((subroutines != null) && (subIndex != maxSub)) {
			System.arraycopy(subroutines, 0, (subroutines = new SubRoutineStatement[subIndex]), 0, subIndex);
		}
	
		// secret local variable for return value (note that this can only occur in a real method)
		if (saveValueNeeded) {
			if (this.saveValueVariable != null) {
				this.saveValueVariable.useFlag = LocalVariableBinding.USED;
			}
		} else {
			this.saveValueVariable = null;
			if (!isSynchronized && this.expression != null && this.expression.resolvedType == BooleanBinding) {
				this.expression.bits |= IsReturnedValue;
			}
		}
		return FlowInfo.DEAD_END;
	}
	 
	/**
	 * Retrun statement code generation
	 *
	 *   generate the finallyInvocationSequence.
	 *
	 * @param currentScope org.eclipse.jdt.internal.compiler.lookup.BlockScope
	 * @param codeStream org.eclipse.jdt.internal.compiler.codegen.CodeStream
	 */
	public void generateCode(BlockScope currentScope, CodeStream codeStream) {
		if ((bits & IsReachable) == 0) {
			return;
		}
		int pc = codeStream.position;
		// generate the expression
		if ((this.expression != null) && (this.expression.constant == Constant.NotAConstant)) {
			this.expression.generateCode(currentScope, codeStream, needValue()); // no value needed if non-returning subroutine
			generateStoreSaveValueIfNecessary(codeStream);
		}
		
		// generation of code responsible for invoking the finally blocks in sequence
		if (subroutines != null) {
			for (int i = 0, max = subroutines.length; i < max; i++) {
				SubRoutineStatement sub = subroutines[i];
				sub.generateSubRoutineInvocation(currentScope, codeStream);
				if (sub.isSubRoutineEscaping()) {
						codeStream.recordPositionsFrom(pc, this.sourceStart);
						SubRoutineStatement.reenterExceptionHandlers(subroutines, i, codeStream);
						return;
				}
				sub.exitAnyExceptionHandler();
			}
		}
		if (saveValueVariable != null) codeStream.load(saveValueVariable);
		
		if ((this.expression != null) && (this.expression.constant != Constant.NotAConstant)) {
			codeStream.generateConstant(this.expression.constant, this.expression.implicitConversion);
			generateStoreSaveValueIfNecessary(codeStream);		
		}
		// output the suitable return bytecode or wrap the value inside a descriptor for doits
		this.generateReturnBytecode(codeStream);
		codeStream.recordPositionsFrom(pc, this.sourceStart);
		SubRoutineStatement.reenterExceptionHandlers(subroutines, -1, codeStream);
	}
	/**
	 * Dump the suitable return bytecode for a return statement
	 *
	 */
	public void generateReturnBytecode(CodeStream codeStream) {
	
		codeStream.generateReturnBytecode(this.expression);
	}
	
	public void generateStoreSaveValueIfNecessary(CodeStream codeStream){
		if (saveValueVariable != null) codeStream.store(saveValueVariable, false);
	}
	public boolean needValue(){
		return (subroutines == null) || (saveValueVariable != null) || isSynchronized;
	}
	public void prepareSaveValueLocation(TryStatement targetTryStatement){
			
		this.saveValueVariable = targetTryStatement.secretReturnValue;
	}
	public StringBuffer printStatement(int tab, StringBuffer output){
	
		printIndent(tab, output).append("return "); //$NON-NLS-1$
		if (this.expression != null )
			this.expression.printExpression(0, output) ;
		return output.append(';');
	}
	
	public void resolve(BlockScope scope) {
		
		MethodScope methodScope = scope.methodScope();
		MethodBinding methodBinding;
		TypeBinding methodType =
			(methodScope.referenceContext instanceof AbstractMethodDeclaration)
				? ((methodBinding = ((AbstractMethodDeclaration) methodScope.referenceContext).binding) == null 
					? null 
					: methodBinding.returnType)
				: VoidBinding;
		TypeBinding expressionType;
		if (methodType == VoidBinding) {
			// the expression should be null
			if (this.expression == null)
				return;
			if ((expressionType = this.expression.resolveType(scope)) != null)
				scope.problemReporter().attemptToReturnNonVoidExpression((/*@OwnPar*/ /*@NoRep*/ ReturnStatement)this, expressionType);
			return;
		}
		if (this.expression == null) {
			if (methodType != null) scope.problemReporter().shouldReturn(methodType, (/*@OwnPar*/ /*@NoRep*/ ReturnStatement)this);
			return;
		}
		this.expression.setExpectedType(methodType); // needed in case of generic method invocation
		if ((expressionType = this.expression.resolveType(scope)) == null) return;
		if (expressionType == VoidBinding) {
			scope.problemReporter().attemptToReturnVoidValue((/*@OwnPar*/ /*@NoRep*/ ReturnStatement)this);
			return;
		}
		if (methodType == null) 
			return;
	
		if (methodType != expressionType) // must call before computeConversion() and typeMismatchError()
			scope.compilationUnitScope().recordTypeConversion(methodType, expressionType);
		if (this.expression.isConstantValueOfTypeAssignableToType(expressionType, methodType)
				|| expressionType.isCompatibleWith(methodType)) {

			this.expression.computeConversion(scope, methodType, expressionType);
			if (expressionType.needsUncheckedConversion(methodType)) {
			    scope.problemReporter().unsafeTypeConversion(this.expression, expressionType, methodType);
			}
			if (this.expression instanceof CastExpression 
					&& (this.expression.bits & (ASTNode.UnnecessaryCast|ASTNode.DisableUnnecessaryCastCheck)) == 0) {
				CastExpression.checkNeedForAssignedCast(scope, methodType, (CastExpression) this.expression);
			}			
			return;
		} else if (scope.isBoxingCompatibleWith(expressionType, methodType)) {
			this.expression.computeConversion(scope, methodType, expressionType);
			if (this.expression instanceof CastExpression 
					&& (this.expression.bits & (ASTNode.UnnecessaryCast|ASTNode.DisableUnnecessaryCastCheck)) == 0) {
				CastExpression.checkNeedForAssignedCast(scope, methodType, (CastExpression) this.expression);
			}			return;
		}
		scope.problemReporter().typeMismatchError(expressionType, methodType, this.expression);
	}
	public void traverse(ASTVisitor visitor, BlockScope scope) {
		if (visitor.visit((/*@OwnPar*/ /*@NoRep*/ ReturnStatement)this, scope)) {
			if (this.expression != null)
				this.expression.traverse(visitor, scope);
		}
		visitor.endVisit((/*@OwnPar*/ /*@NoRep*/ ReturnStatement)this, scope);
	}
}
