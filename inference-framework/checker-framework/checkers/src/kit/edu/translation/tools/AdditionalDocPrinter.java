package kit.edu.translation.tools;

import com.sun.source.tree.MethodTree;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.Pretty;
import com.sun.source.util.TreePath;

import java.io.IOException;
import java.io.Writer;
import java.util.List;
import java.util.Map;

public class AdditionalDocPrinter extends Pretty {

    /** Stores for methods a list of additional docstring lines. */
    private Map<MethodTree, List<String>> documentation;

    public AdditionalDocPrinter(Writer out, boolean sourceOutput) {
        super(out, sourceOutput);
    }

    public AdditionalDocPrinter(Writer out, boolean sourceOutput, Map<MethodTree, List<String>> documentation) {
        super(out, sourceOutput);
        this.documentation = documentation;
    }

    public void visitMethodDef(JCTree.JCMethodDecl tree) {
        if (documentation.containsKey(tree)) {
            try {
                for (String doc_line : documentation.get(tree)) {
                    this.println();
                    this.align();
                    this.print(doc_line);
                }
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }
        super.visitMethodDef(tree);
    }
}
