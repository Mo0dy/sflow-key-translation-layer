package checkers.inference.sflow;

import checkers.source.Result;
import checkers.types.AnnotatedTypeMirror;
import com.sun.source.tree.*;
import checkers.util.ElementUtils;
import checkers.util.TreeUtils;
import com.sun.source.util.TreePath;
import kit.edu.translation.core.SafeObservationExpression;
import kit.edu.translation.tools.AdditionalDocPrinter;
import kit.edu.translation.tools.ObservationJMLTranslator;
import kit.edu.translation.tools.TranslatedSourceWriter;

import javax.lang.model.element.Modifier;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.*;

public class SFlowVisitor extends SFlowBaseVisitor {
    // @Felix: @TODO: Get this from the command line
    private final String TEMP_DIR = "/home/felix/Downloads/sflowtranslationlayer";
    private final String BASE_PATH = "/home/felix/_Uni/BA/Java_Tests";

    /* Stores if the types are evaluated in a tainted context. */
    private boolean conditionedOnTainted = false;

    /** Stores for methods a list of additional docstring lines. */
    private TranslatedSourceWriter writer;

    public SFlowVisitor(SFlowChecker checker, CompilationUnitTree root) {
        super(checker, root);
        writer = new TranslatedSourceWriter(root);
    }

    @Override
    public void visit(TreePath path) {
        this.scan(path, null);
        this.create_key_file(path);
    }

    @Override
    public Void visitIf(IfTree node, Void p) {
        ExpressionTree condition = node.getCondition();
        AnnotatedTypeMirror conditionType = atypeFactory.getAnnotatedType(condition);
        if (conditionType.hasAnnotation(SFlowChecker.TAINTED) && !conditionedOnTainted) {
            conditionedOnTainted = true;
            Void result = super.visitIf(node, p);
            conditionedOnTainted = false;
            return result;
        } else {
            return super.visitIf(node, p);
        }
    }

    @Override
    protected void commonAssignmentCheck(AnnotatedTypeMirror varType, AnnotatedTypeMirror valueType, Tree valueTree, String errorKey) {
        super.commonAssignmentCheck(varType, valueType, valueTree, errorKey);

        if (conditionedOnTainted && varType.hasAnnotation(SFlowChecker.SAFE)) {
            checker.report(Result.failure("implicit flow", varType, valueType), valueTree);
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

    private static String getDeterminesClause(List<String> safeVars, boolean safeResult) {
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

    public List<VariableTree> getSafeClassVariables(ClassTree classTree) {
        List<VariableTree> safeVariableNames = new ArrayList<VariableTree>();
        // find all SAFE class variables:
        for (Tree variableTree : classTree.getMembers()) {
            AnnotatedTypeMirror variableType = atypeFactory.getAnnotatedType(variableTree);
            if (variableType.hasAnnotation(SFlowChecker.SAFE)) {
                safeVariableNames.add(((VariableTree) variableTree));
            }
        }

        // recursively call for super class
        if (classTree.getExtendsClause() != null) {
            AnnotatedTypeMirror.AnnotatedDeclaredType superClassType = (AnnotatedTypeMirror.AnnotatedDeclaredType) atypeFactory.getAnnotatedType(classTree.getExtendsClause());
            ClassTree superClassTree = (ClassTree) trees.getTree(superClassType.getUnderlyingType().asElement());
            safeVariableNames.addAll(getSafeClassVariables(superClassTree));
        }
        return safeVariableNames;
    }

    public SafeObservationExpression createSafeObservationExpression(MethodTree node) {
        AnnotatedTypeMirror.AnnotatedExecutableType methodType = atypeFactory.getAnnotatedType(node);
        List<AnnotatedTypeMirror> parameterTypes = methodType.getParameterTypes();

        // Find out if Method is static without using TreeUtils
        boolean isStatic = ElementUtils.isStatic(TreeUtils.elementFromDeclaration(node));

        List<VariableTree> safeVariables;
        if (isStatic) {
            safeVariables = new ArrayList<VariableTree>();
        } else {
            // TODO: @Felix filter by used variables
            ClassTree classTree = visitorState.getClassTree();
            safeVariables = getSafeClassVariables(classTree);
        }

        for (int i = 0; i < parameterTypes.size(); i++) {
            AnnotatedTypeMirror parameterType = parameterTypes.get(i);
            if (parameterType.hasAnnotation(SFlowChecker.SAFE)) {
                safeVariables.add(node.getParameters().get(i));
            }
        }

        boolean safeResult = methodType.getReturnType().hasAnnotation(SFlowChecker.SAFE);
        // Handle constructors
        if (TreeUtils.isConstructor(node)) {
            safeResult = false;
        }

        return new SafeObservationExpression(safeVariables, safeResult);
    }

    @Override
    public Void visitMethod(MethodTree node, Void p) {
        // @Felix: @TODO: what to do for poly types
        checker.resetWarningAndErrorFlags();
        Void result = super.visitMethod(node, p);

        List<String> jmlComment = ObservationJMLTranslator.TranslateSafeObservationToJML(
                createSafeObservationExpression(node)
        );

        if (checker.getWarningOrErrorSinceReset()) {
            // @Felix: @TODO: Output warning to console that this method should be verified by KeY
            writer.addDocumentationLine(node, "/* @Key: Verify this method. */");
        }
        writer.addDocumentationLines(node, jmlComment);
        return result;
    }

    private void create_key_file(TreePath path) {
        // @Felix: @TODO: In the Checker remove the temp folder
        // @Felix: Output, FileCreation
        String originalPath = path.getCompilationUnit().getSourceFile().getName();

        String relativePath = originalPath.substring(BASE_PATH.length());
        String outputPath = TEMP_DIR + relativePath;
        File outputFile = new File(outputPath);
        File outputDir = outputFile.getParentFile();

        System.out.println("=====================================");
        System.out.println("Creating output file: " + outputFile);
        System.out.println("=====================================");

        try {
            // Create the output directory if it doesn't exist
            if (!outputDir.exists()) {
                if (!outputDir.mkdirs()) {
                    throw new RuntimeException("Failed to create output directory: " + outputDir);
                }
            }

            // Create the output file if it doesn't exist
            if (!outputFile.exists()) {
                if (!outputFile.createNewFile()) {
                    throw new RuntimeException("Failed to create output file: " + outputFile);
                }
            }

            writer.writeToFile(outputFile);
        } catch (IOException e) {
            throw new RuntimeException("Could not write KeY input file: " + e);
        }
    }
}
