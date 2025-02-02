package checkers.inference.sflow;

import checkers.inference.sflow.quals.SafeMethod;
import checkers.inference.sflow.quals.TaintedMethod;
import checkers.source.Result;
import checkers.types.AnnotatedTypeMirror;
import checkers.util.AnnotationUtils;
import checkers.util.ElementUtils;
import checkers.util.TreeUtils;
import com.sun.source.tree.*;
import com.sun.source.util.TreePath;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ExecutableElement;

import kit.edu.translation.core.SafeObservationExpression;
import kit.edu.translation.tools.JMLBuilder;
import kit.edu.translation.tools.TranslatedSourceWriter;

public class SFlowVisitor extends SFlowBaseVisitor {

    private final AnnotationMirror TAINTED_METHOD;
    private final AnnotationMirror SAFE_METHOD;

    /* Stores if the types are evaluated in a tainted context. */
    private boolean conditionedOnTainted = false;

    /**
     * Stores for methods a list of additional docstring lines.
     */
    private final TranslatedSourceWriter writer;

    public SFlowVisitor(SFlowChecker checker, CompilationUnitTree root) {
        super(checker, root);
        TAINTED_METHOD = checker.annoFactory.fromClass(TaintedMethod.class);
        SAFE_METHOD = checker.annoFactory.fromClass(SafeMethod.class);
        writer = new TranslatedSourceWriter(root);
    }

    @Override
    public void visit(TreePath path) {
        this.scan(path, null);
        this.create_key_file(path);
    }

    private boolean isTaintedCondition(ExpressionTree condition) {
        return atypeFactory.getAnnotatedType(condition).hasAnnotation(
                SFlowChecker.TAINTED);
    }

    @Override
    public Void visitIf(IfTree node, Void p) {
        if (isTaintedCondition(node.getCondition()) && !conditionedOnTainted) {
            conditionedOnTainted = true;
            Void result = super.visitIf(node, p);
            conditionedOnTainted = false;
            return result;
        } else {
            return super.visitIf(node, p);
        }
    }

    @Override
    public Void visitWhileLoop(WhileLoopTree node, Void unused) {
        if (isTaintedCondition(node.getCondition()) && !conditionedOnTainted) {
            conditionedOnTainted = true;
            Void result = super.visitWhileLoop(node, unused);
            conditionedOnTainted = false;
            return result;
        } else {
            return super.visitWhileLoop(node, unused);
        }
    }

    @Override
    public Void visitDoWhileLoop(DoWhileLoopTree node, Void unused) {
        if (isTaintedCondition(node.getCondition()) && !conditionedOnTainted) {
            conditionedOnTainted = true;
            Void result = super.visitDoWhileLoop(node, unused);
            conditionedOnTainted = false;
            return result;
        } else {
            return super.visitDoWhileLoop(node, unused);
        }
    }

    @Override
    public Void visitForLoop(ForLoopTree node, Void unused) {
        if (isTaintedCondition(node.getCondition()) && !conditionedOnTainted) {
            conditionedOnTainted = true;
            Void result = super.visitForLoop(node, unused);
            conditionedOnTainted = false;
            return result;
        } else {
            return super.visitForLoop(node, unused);
        }
    }

    @Override
    public Void visitEnhancedForLoop(EnhancedForLoopTree node, Void p) {
        // Print forloop
        if (isTaintedCondition(node.getExpression()) && !conditionedOnTainted) {
            conditionedOnTainted = true;
            Void result = super.visitEnhancedForLoop(node, p);
            conditionedOnTainted = false;
            return result;
        } else {
            return super.visitEnhancedForLoop(node, p);
        }
    }

    @Override
    public Void visitSwitch(SwitchTree node, Void unused) {
        if (isTaintedCondition(node.getExpression()) && !conditionedOnTainted) {
            conditionedOnTainted = true;
            Void result = super.visitSwitch(node, unused);
            conditionedOnTainted = false;
            return result;
        } else {
            return super.visitSwitch(node, unused);
        }
    }

    @Override
    public Void visitThrow(ThrowTree node, Void unused) {
        if (conditionedOnTainted) {
            checker.report(
                    Result.failure(
                            "Throwing under tainted condition can produce implicit flow."),
                    node);
        }
        return super.visitThrow(node, unused);
    }

    @Override
    public Void visitReturn(ReturnTree node, Void p) {
        if (conditionedOnTainted) {
            checker.report(Result.failure("implicit flow"), node);
        }
        return super.visitReturn(node, p);
    }

    @Override
    public Void visitBreak(BreakTree node, Void unused) {
        if (conditionedOnTainted) {
            checker.report(Result.failure("implicit flow"), node);
        }
        return super.visitBreak(node, unused);
    }

    @Override
    public Void visitContinue(ContinueTree node, Void unused) {
        if (conditionedOnTainted) {
            checker.report(Result.failure("implicit flow"), node);
        }
        return super.visitContinue(node, unused);
    }

    @Override
    protected void commonAssignmentCheck(AnnotatedTypeMirror varType,
                                         AnnotatedTypeMirror valueType,
                                         Tree valueTree, String errorKey) {
        super.commonAssignmentCheck(varType, valueType, valueTree, errorKey);

        if (conditionedOnTainted && varType.hasAnnotation(SFlowChecker.SAFE)) {
            checker.report(Result.failure("implicit flow", varType, valueType),
                    valueTree);
        }
    }

    private static String getObservationExpression(List<String> vars) {
        if (vars.size() == 0) {
            return "\\nothing";
        }

        StringBuilder result = new StringBuilder();
        int size = vars.size();
        for (int i = 0; i < size; i++) {
            result.append(vars.get(i));
            if (i != size - 1) {
                result.append(", ");
            }
        }
        return result.toString();
    }

    private static String getDeterminesClause(List<String> safeVars,
                                              boolean safeResult) {
        StringBuilder result = new StringBuilder("determines ");
        if (safeResult) {
            List<String> allSafeVars = new ArrayList<String>(safeVars);
            allSafeVars.add("\\result");
            result.append(getObservationExpression(allSafeVars));
        } else {
            result.append(getObservationExpression(safeVars));
        }
        result.append(" \\by ");
        result.append(getObservationExpression(safeVars));
        result.append(";");
        return result.toString();
    }

    private static List<String> makeJMLComment(List<String> lines) {
        List<String> result = new ArrayList<String>();
        result.add("/*@");
        for (String line : lines) {
            result.add("  @ " + line);
        }
        result.add("  @*/");
        return result;
    }

    // @Felix: @TODO: Make this a subtype check rather than a simple hasAnnotation
    // check
    public List<VariableTree> getClassVariables(ClassTree classTree,
                                                AnnotationMirror annotation) {
        List<VariableTree> safeVariableNames = new ArrayList<VariableTree>();
        // find all SAFE class variables:
        for (Tree variableTree : classTree.getMembers()) {
            AnnotatedTypeMirror variableType =
                    atypeFactory.getAnnotatedType(variableTree);
            if (variableType.hasAnnotation(annotation)) {
                safeVariableNames.add(((VariableTree) variableTree));
            }
        }

        // recursively call for super class
        if (classTree.getExtendsClause() != null) {
            AnnotatedTypeMirror.AnnotatedDeclaredType superClassType =
                    (AnnotatedTypeMirror.AnnotatedDeclaredType)
                            atypeFactory.getAnnotatedType(classTree.getExtendsClause());
            ClassTree superClassTree = (ClassTree) trees.getTree(
                    superClassType.getUnderlyingType().asElement());
            safeVariableNames.addAll(getClassVariables(superClassTree, annotation));
        }
        return safeVariableNames;
    }

    public SafeObservationExpression
    createSafeObservationExpression(MethodTree node) {
        AnnotatedTypeMirror.AnnotatedExecutableType methodType =
                atypeFactory.getAnnotatedType(node);
        List<AnnotatedTypeMirror> parameterTypes = methodType.getParameterTypes();

        // Find out if Method is static without using TreeUtils
        boolean isStatic =
                ElementUtils.isStatic(TreeUtils.elementFromDeclaration(node));

        List<VariableTree> safeVariables;
        if (isStatic) {
            safeVariables = new ArrayList<VariableTree>();
        } else {
            // TODO: @Felix filter by used variables
            ClassTree classTree = visitorState.getClassTree();
            safeVariables = getClassVariables(classTree, SFlowChecker.SAFE);
        }

        for (int i = 0; i < parameterTypes.size(); i++) {
            AnnotatedTypeMirror parameterType = parameterTypes.get(i);
            if (parameterType.hasAnnotation(SFlowChecker.SAFE)) {
                safeVariables.add(node.getParameters().get(i));
            }
        }

        boolean safeResult =
                methodType.getReturnType().hasAnnotation(SFlowChecker.SAFE);
        // Handle constructors
        if (TreeUtils.isConstructor(node)) {
            safeResult = false;
        }

        return new SafeObservationExpression(safeVariables, safeResult);
    }

    @Override
    public Void visitMethodInvocation(MethodInvocationTree node, Void p) {
        Void result = super.visitMethodInvocation(node, p);

        if (conditionedOnTainted && !isTaintedMethod(node)) {
            checker.report(
                    Result.failure("implicit flow method needs to be @TaintedMethod",
                            node),
                    node);
        }

        return result;
    }

    private AnnotationMirror
    extractMethodTypeAnnotation(List<AnnotationMirror> methodAnnotations,
                                String methodName) {
        boolean containsTaintedMethod =
                AnnotationUtils.containsSame(methodAnnotations, TAINTED_METHOD);
        boolean containsSafeMethod =
                AnnotationUtils.containsSame(methodAnnotations, SAFE_METHOD);

        if (containsTaintedMethod && containsSafeMethod) {
            checker.errorAbort("Method " + methodName + " is both @TaintedMethod and "
                    + "@SafeMethod.");
        }
        if (containsTaintedMethod) {
            return TAINTED_METHOD;
        }

        // Use default method type.
        return SAFE_METHOD;
    }

    public boolean isTaintedMethod(MethodInvocationTree node) {
        List<? extends AnnotationMirror> annotations =
                TreeUtils.elementFromUse(node).getAnnotationMirrors();
        List<AnnotationMirror> annotationsNew =
                new ArrayList<AnnotationMirror>(annotations);
        return AnnotationUtils.areSame(extractMethodTypeAnnotation(
                        annotationsNew, node.getMethodSelect().toString()),
                TAINTED_METHOD);
    }

    public boolean isTaintedMethod(MethodTree node) {
        List<? extends AnnotationMirror> annotations =
                TreeUtils.elementFromDeclaration(node).getAnnotationMirrors();
        List<AnnotationMirror> annotationsNew =
                new ArrayList<AnnotationMirror>(annotations);
        return AnnotationUtils.areSame(extractMethodTypeAnnotation(
                        annotationsNew, node.getName().toString()),
                TAINTED_METHOD);
    }

    public boolean isTaintedMethod(ExecutableElement element) {
        List<? extends AnnotationMirror> annotations =
                element.getAnnotationMirrors();
        List<AnnotationMirror> annotationsNew =
                new ArrayList<AnnotationMirror>(annotations);
        return AnnotationUtils.areSame(extractMethodTypeAnnotation(
                        annotationsNew, element.getSimpleName().toString()),
                TAINTED_METHOD);
    }

    @Override
    protected boolean checkOverride(MethodTree overriderTree, AnnotatedTypeMirror.AnnotatedDeclaredType enclosingType, AnnotatedTypeMirror.AnnotatedExecutableType overridden, AnnotatedTypeMirror.AnnotatedDeclaredType overriddenType, Void p) {
        boolean overriderIsTaintedMethod = isTaintedMethod(overriderTree);
        boolean overriddenIsTaintedMethod = isTaintedMethod(overridden.getElement());
        // annotations need to be contravariant
        if (!overriderIsTaintedMethod && overriddenIsTaintedMethod) {
            checker.report(Result.failure("overriding @TaintedMethod with @SafeMethod",
                    overriderTree), overriderTree);
        }
        return super.checkOverride(overriderTree, enclosingType, overridden, overriddenType, p);
    }

    @Override
    public Void visitMethod(MethodTree node, Void p) {
        // @Felix: @TODO: what to do for poly types
        checker.resetWarningAndErrorFlags();

        boolean safeMethod = isTaintedMethod(node);
        if (safeMethod) {
            assert (!conditionedOnTainted);
            conditionedOnTainted = true;
        }

        Void result = super.visitMethod(node, p);
        conditionedOnTainted = false;

        if (checker.getWarningOrErrorSinceReset()) {
            // @Felix: @TODO: Output warning to console that this method should be
            // verified by KeY
            writer.addDocumentationLine(node, "/* @Key: Verify this method. */");
        }

        JMLBuilder jmlBuilder = new JMLBuilder();
        jmlBuilder.addSafeObservation(createSafeObservationExpression(node));

        // TODO: what should be / shouldn't be assignable in a static method?
        if (safeMethod && !ElementUtils.isStatic(TreeUtils.elementFromDeclaration(node))) {
            jmlBuilder.addAssignsClause(
                    getClassVariables(visitorState.getClassTree(), SFlowChecker.TAINTED));
        }

        writer.addDocumentationLines(node, jmlBuilder.makeJMLComment());
        return result;
    }

    private void create_key_file(TreePath path) {
        // @Felix: @TODO: In the Checker remove the temp folder
        String originalPath = path.getCompilationUnit().getSourceFile().getName();
        String relativePath =
                originalPath.substring(checker.getBasePath().length());
        String outputPath = checker.getTempDir() + relativePath;
        File outputFile = new File(outputPath);
        File outputDir = outputFile.getParentFile();

        System.out.println("=====================================");
        System.out.println("Creating output file: " + outputFile);
        System.out.println("=====================================");

        try {
            // Create the output directory if it doesn't exist
            if (!outputDir.exists()) {
                if (!outputDir.mkdirs()) {
                    throw new RuntimeException("Failed to create output directory: " +
                            outputDir);
                }
            }

            // Create the output file if it doesn't exist
            if (!outputFile.exists()) {
                if (!outputFile.createNewFile()) {
                    throw new RuntimeException("Failed to create output file: " +
                            outputFile);
                }
            }

            writer.writeToFile(outputFile);
        } catch (IOException e) {
            throw new RuntimeException("Could not write KeY input file: " + e);
        }
    }
}
