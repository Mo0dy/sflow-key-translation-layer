package kit.edu.translation.tools;

import com.sun.source.tree.VariableTree;
import kit.edu.translation.core.SafeObservationExpression;

import java.util.ArrayList;
import java.util.List;

public class JMLBuilder {
    List<String> lines = new ArrayList<String>();

    public JMLBuilder() {
    }

    public List<String> makeJMLComment() {
        List<String> result = new ArrayList<String>();
        result.add("/*@");
        for (String line : lines) {
            result.add("  @ " + line);
        }
        result.add("  @*/");
        return result;
    }

    private static String getVarList(List<String> vars) {
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

    private static String getDeterminesClause(SafeObservationExpression oexpr) {
        StringBuilder result = new StringBuilder("determines ");
        List<String> observedVars = toStringVars(oexpr.safeVariables);
        if (oexpr.safeResult) {
            observedVars.add("\\result");
        }
        result.append(getVarList(observedVars));
        result.append(" \\by ");
        if (oexpr.safeResult) {
            // \result only appears in the first part of the determines clause
            observedVars.remove(observedVars.size() - 1);
        }
        result.append(getVarList(observedVars));
        result.append(";");
        return result.toString();
    }
    public JMLBuilder addSafeObservation(SafeObservationExpression safeObservationExpression) {
        lines.add(getDeterminesClause(safeObservationExpression));
        return this;
    }

    public JMLBuilder addAssignsClause(List<VariableTree> vars) {
        lines.add("assignable " + getVarList(toStringVars(vars)) + ";");
        return this;
    }

    private static List<String> toStringVars(List<VariableTree> vars) {
        List<String> result = new ArrayList<String>();
        for (VariableTree var : vars) {
            result.add(var.getName().toString());
        }
        return result;
    }
}
