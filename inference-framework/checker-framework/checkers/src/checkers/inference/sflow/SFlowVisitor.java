package checkers.inference.sflow;

import com.sun.source.tree.CompilationUnitTree;

public class SFlowVisitor extends SFlowBaseVisitor {
    public SFlowVisitor(SFlowChecker checker, CompilationUnitTree root) {
        super(checker, root);
    }
}
