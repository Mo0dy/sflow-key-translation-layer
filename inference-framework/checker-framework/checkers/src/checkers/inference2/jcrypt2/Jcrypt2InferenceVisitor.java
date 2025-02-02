package checkers.inference2.jcrypt2;

import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.CompilationUnitTree;
import com.sun.source.tree.ExpressionTree;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.Tag;

import checkers.inference2.InferenceChecker;
import checkers.inference2.Reference;
import checkers.inference2.jcrypt.JcryptInferenceVisitor;

public class Jcrypt2InferenceVisitor extends JcryptInferenceVisitor {
	
	//public static Map<ExpressionTree, Reference> memberSelectRefs = new HashMap<>();
	
	public Jcrypt2InferenceVisitor(InferenceChecker checker,
			CompilationUnitTree root) {
		super(checker, root);
	}
		
	@Override
	public void processBinaryTree(Reference lhsRef, BinaryTree bTree) {
		Reference ref = checker.getAnnotatedReference(bTree);
		ExpressionTree left = bTree.getLeftOperand();
		ExpressionTree right = bTree.getRightOperand();
		Reference leftRef = checker.getAnnotatedReference(left);
		Reference rightRef = checker.getAnnotatedReference(right);
		if (!checker.containsAnno(leftRef, ((Jcrypt2Checker) checker).CLEAR)
				|| ((JCBinary) bTree).getTag() != Tag.MUL) {
			checker.addSubtypeConstraint(leftRef, ref, ((JCTree) left).getStartPosition());
		}
		if (!checker.containsAnno(rightRef, ((Jcrypt2Checker) checker).CLEAR)
				|| ((JCBinary) bTree).getTag() != Tag.MUL) {
			checker.addSubtypeConstraint(rightRef, ref, ((JCTree) right).getStartPosition());
		}
		if (lhsRef != null) {
			checker.addSubtypeConstraint(ref, lhsRef, ((JCTree) left).getStartPosition());
		}
		generateConstraint(leftRef, left);
		generateConstraint(rightRef, right);
    }
		
}
