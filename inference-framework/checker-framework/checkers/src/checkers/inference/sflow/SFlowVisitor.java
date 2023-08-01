package checkers.inference.sflow;

import checkers.types.AnnotatedTypeMirror;
import com.sun.source.tree.*;
import checkers.util.TreeUtils;
import com.sun.source.util.TreePath;
import kit.edu.translation.tools.AdditionalDocPrinter;

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
    private Map<MethodTree, List<String>> documentationStore;

    public SFlowVisitor(SFlowChecker checker, CompilationUnitTree root) {
        super(checker, root);
        documentationStore = new HashMap<MethodTree, List<String>>();
    }

    @Override
    public void visit(TreePath path) {
        this.scan(path, null);
        this.create_key_file(path);
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

    public List<String> getSafeClassVariables(ClassTree classTree) {
        List<String> safeVariableNames = new ArrayList<String>();
        // find all SAFE class variables:
        for (Tree variableTree : classTree.getMembers()) {
            AnnotatedTypeMirror variableType = atypeFactory.getAnnotatedType(variableTree);
            if (variableType.hasAnnotation(SFlowChecker.SAFE)) {
                safeVariableNames.add(((VariableTree) variableTree).getName().toString());
            }
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
        boolean isStatic = node.getModifiers().getFlags().contains(Modifier.STATIC);

        List<String> safeVariableNames;
        if (isStatic) {
            safeVariableNames = new ArrayList<String>();
        } else {
            // TODO: @Felix filter by used variables
            ClassTree classTree = visitorState.getClassTree();
            safeVariableNames = getSafeClassVariables(classTree);
        }

        for (int i = 0; i < parameterTypes.size(); i++) {
            AnnotatedTypeMirror parameterType = parameterTypes.get(i);
            if (parameterType.hasAnnotation(SFlowChecker.SAFE)) {
                safeVariableNames.add(node.getParameters().get(i).getName().toString());
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

        String determinesClause = getDeterminesClause(safeVariableNames, safeResult);
        List<String> jmlComment = makeJMLComment(Collections.singletonList(determinesClause));

        if (this.checker.getWarningOrErrorSinceReset()) {
            addDocumentationLine(node, "/* @Key: Verify this method. */");
//            System.out.println("=====================================");
//            System.out.println("Error found in method: " + node.getName());
//            System.out.println("=====================================");
        }
        addDocumentationLines(node, jmlComment);
        return result;
    }

    private void write_header(PrintWriter writer) {
        writer.println("// This file was autmaticaly generated by the Translation layer at: " + new java.util.Date());
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

            // Write the pretty-printed contents to the output file
            PrintWriter writer = new PrintWriter(new FileWriter(outputFile));
            this.write_header(writer);
            AdditionalDocPrinter pretty = new AdditionalDocPrinter(writer, true, documentationStore);
            pretty.printTreePath(path);
            writer.close();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    public void addDocumentationLines(MethodTree method, List<String> doc_lines) {
        if (documentationStore.containsKey(method)) {
            documentationStore.get(method).addAll(doc_lines);
        } else {
            documentationStore.put(method, new ArrayList<String>());
            documentationStore.get(method).addAll(doc_lines);
        }
    }

    public void addDocumentationLine(MethodTree method, String doc_line) {
        if (documentationStore.containsKey(method)) {
            documentationStore.get(method).add(doc_line);
        } else {
            documentationStore.put(method, new ArrayList<String>());
            documentationStore.get(method).add(doc_line);
        }
    }

}
