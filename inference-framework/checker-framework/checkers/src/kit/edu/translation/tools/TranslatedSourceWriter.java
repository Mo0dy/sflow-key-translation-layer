package kit.edu.translation.tools;

import com.sun.source.tree.CompilationUnitTree;
import com.sun.source.tree.MethodTree;
import com.sun.tools.javac.tree.JCTree;

import java.io.*;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class TranslatedSourceWriter {
    private CompilationUnitTree compilationUnit;
    private Map<MethodTree, List<String>> additionalMethodComments;

    public TranslatedSourceWriter(CompilationUnitTree root) {
        this.compilationUnit = root;
        additionalMethodComments = new HashMap<MethodTree, List<String>>();
    }

    public void writeToFile(File file) throws IOException {
        PrintWriter writer = new PrintWriter(new FileWriter(file));
        write(writer);
        writer.close();
    }

    public void write(Writer out) throws IOException {
        AdditionalDocPrinter printer = new AdditionalDocPrinter(out, true, additionalMethodComments);
            out.write("// This file was automatically generated by the Translation layer at: " + new java.util.Date() + "\n");
            printer.printUnit((JCTree.JCCompilationUnit) compilationUnit, null);
    }

    public void addDocumentationLines(MethodTree method, List<String> doc_lines) {
        if (additionalMethodComments.containsKey(method)) {
            additionalMethodComments.get(method).addAll(doc_lines);
        } else {
            additionalMethodComments.put(method, new ArrayList<String>());
            additionalMethodComments.get(method).addAll(doc_lines);
        }
    }

    public void addDocumentationLine(MethodTree method, String doc_line) {
        if (additionalMethodComments.containsKey(method)) {
            additionalMethodComments.get(method).add(doc_line);
        } else {
            additionalMethodComments.put(method, new ArrayList<String>());
            additionalMethodComments.get(method).add(doc_line);
        }
    }
}