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
import org.eclipse.jdt.internal.compiler.classfmt.ClassFileConstants;
import org.eclipse.jdt.internal.compiler.impl.Constant;
import org.eclipse.jdt.internal.compiler.lookup.*;

public class JavadocArgumentExpression extends Expression {
	public char[] token;
	public /*@RepNorep*/ Argument argument;

	public JavadocArgumentExpression(char[] name, int startPos, int endPos, TypeReference typeRef) {
		this.token = name;
		this.sourceStart = startPos;
		this.sourceEnd = endPos;
		long pos = (((long) startPos) << 32) + endPos;
		this.argument = new Argument(name, pos, typeRef, ClassFileConstants.AccDefault);
		this.bits |= InsideJavadoc;
	}

	/*
	 * Resolves type on a Block or Class scope.
	 */
	private TypeBinding internalResolveType(Scope scope) {
		this.constant = Constant.NotAConstant;
		if (this.resolvedType != null) // is a shared type reference which was already resolved
			return this.resolvedType.isValidBinding() ? this.resolvedType : null; // already reported error

		if (this.argument != null) {
			TypeReference typeRef = this.argument.type;
			if (typeRef != null) {
				this.resolvedType = typeRef.getTypeBinding(scope);
				typeRef.resolvedType = this.resolvedType;
				if (!this.resolvedType.isValidBinding()) {
					scope.problemReporter().javadocInvalidType(typeRef, this.resolvedType, scope.getDeclarationModifiers());
					return null;
				}
				if (isTypeUseDeprecated(this.resolvedType, scope)) {
					scope.problemReporter().javadocDeprecatedType(this.resolvedType, typeRef, scope.getDeclarationModifiers());
					return null;
				}
				return this.resolvedType = scope.environment().convertToRawType(this.resolvedType);
			}
		}
		return null;
	}
	
	public StringBuffer printExpression(int indent, StringBuffer output) {
		if (this.argument == null) {
			if (this.token != null) {
				output.append(this.token);
			}
		}
		else {
			this.argument.print(indent, output);
		}
		return output;
	}

	public void resolve(BlockScope scope) {
		if (this.argument != null) {
			this.argument.resolve(scope);
		}
	}

	public TypeBinding resolveType(BlockScope scope) {
		return internalResolveType(scope);
	}

	public TypeBinding resolveType(ClassScope scope) {
		return internalResolveType(scope);
	}

	/* (non-Javadoc)
	 * Redefine to capture javadoc specific signatures
	 * @see org.eclipse.jdt.internal.compiler.ast.ASTNode#traverse(org.eclipse.jdt.internal.compiler.ASTVisitor, org.eclipse.jdt.internal.compiler.lookup.BlockScope)
	 */
	public void traverse(ASTVisitor visitor, BlockScope blockScope) {
		if (visitor.visit((/*@OwnPar*/ /*@NoRep*/ JavadocArgumentExpression)this, blockScope)) {
			if (this.argument != null) {
				this.argument.traverse(visitor, blockScope);
			}
		}
		visitor.endVisit((/*@OwnPar*/ /*@NoRep*/ JavadocArgumentExpression)this, blockScope);
	}
}
