package kit.edu.translation.core;

import com.sun.source.tree.VariableTree;

import java.util.List;

public class SafeObservationExpression {
    public List<VariableTree> safeVariables;
    public boolean safeResult;

    public SafeObservationExpression(List<VariableTree> safeVariables, boolean safeResult) {
        this.safeVariables = safeVariables;
        this.safeResult = safeResult;
    }
}
