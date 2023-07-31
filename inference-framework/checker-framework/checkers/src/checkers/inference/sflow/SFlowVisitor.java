package checkers.inference.sflow;

import com.sun.source.tree.CompilationUnitTree;
import com.sun.source.tree.MethodTree;
import com.sun.source.util.TreePath;
import kit.edu.translation.tools.TranslationPrinter;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;

public class SFlowVisitor extends SFlowBaseVisitor {
    // @Felix: @TODO: Get this from the command line
    private final String TEMP_DIR = "/home/felix/Downloads/sflowtranslationlayer";
    private final String BASE_PATH = "/home/felix/_Uni/BA/Java_Tests";

    public SFlowVisitor(SFlowChecker checker, CompilationUnitTree root) {
        super(checker, root);
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
            System.out.println("=====================================");
            System.out.println("Error found in method: " + node.getName());
            System.out.println("=====================================");
        }
        return result;
    }

    private void create_key_file(TreePath path) {
        // @Felix: Output, FileCreation
        String originalPath = path.getCompilationUnit().getSourceFile().getName();

        String relativePath = originalPath.substring(BASE_PATH.length());
        String outputPath = TEMP_DIR + relativePath;
        File outputFile = new File(outputPath);
        File outputDir = outputFile.getParentFile();

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
            TranslationPrinter pretty = new TranslationPrinter(writer, true);
            pretty.printTreePath(path);
            writer.close();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }
}
