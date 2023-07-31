package kit.edu.translation.tools;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.Pretty;
import com.sun.source.util.TreePath;

import java.io.IOException;
import java.io.Writer;

public class TranslationPrinter extends Pretty {
    public TranslationPrinter(Writer out, boolean sourceOutput) {
        super(out, sourceOutput);
    }

    public void printTreePath(TreePath path) throws IOException {
        printExpr((JCTree) path.getLeaf());
    }
}
