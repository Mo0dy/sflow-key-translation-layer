package checkers.inference.sflow;

import checkers.units.quals.A;
import com.sun.source.tree.CompilationUnitTree;
import com.sun.source.tree.MethodTree;
import com.sun.source.util.TreePath;
import kit.edu.translation.tools.AdditionalDocPrinter;

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

    @Override
    public Void visitMethod(MethodTree node, Void p) {
        this.checker.resetWarningAndErrorFlags();
        Void result = super.visitMethod(node, p);
        if (this.checker.getWarningOrErrorSinceReset()) {
            addDocumentationLine(node, "/* WARNING: This method contains errors. */");
            System.out.println("=====================================");
            System.out.println("Error found in method: " + node.getName());
            System.out.println("=====================================");
        }
        return result;
    }

    private void write_header(PrintWriter writer) {
        writer.println("// This file was autmaticaly generated by the Translation layer at: " + new java.util.Date());
    }

    private void create_key_file(TreePath path) {
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

    public void addDocumentationLine(MethodTree method, String doc_line) {
        if (documentationStore.containsKey(method)) {
            documentationStore.get(method).add(doc_line);
        } else {
            documentationStore.put(method, new ArrayList<String>());
            documentationStore.get(method).add(doc_line);
        }
    }

}
