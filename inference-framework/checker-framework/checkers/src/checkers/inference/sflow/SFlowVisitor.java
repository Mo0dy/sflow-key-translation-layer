package checkers.inference.sflow;

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

    @Override
    public Void visitMethod(MethodTree node, Void p) {
        // @Felix: @TODO: what to do for poly types
        this.checker.resetWarningAndErrorFlags();
        Void result = super.visitMethod(node, p);

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


        System.out.println("=====================================");
        System.out.println("Method: " + node.getName());
        System.out.println("Method type: " + methodType);
        System.out.println("Return type: " + methodType.getReturnType());
        System.out.println("Is constructor: " + TreeUtils.isConstructor(node));
        System.out.println("=====================================");

        boolean safeResult = methodType.getReturnType().hasAnnotation(SFlowChecker.SAFE);
        // Handle constructors
        if (TreeUtils.isConstructor(node)) {
            safeResult = false;
        }

        List<String> jmlComment = ObservationJMLTranslator.TranslateSafeObservationToJML(
                new SafeObservationExpression(safeVariables, safeResult)
        );

        if (this.checker.getWarningOrErrorSinceReset()) {
            writer.addDocumentationLine(node, "/* @Key: Verify this method. */");
//            System.out.println("=====================================");
//            System.out.println("Error found in method: " + node.getName());
//            System.out.println("=====================================");
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
