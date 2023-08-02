package kit.edu.translation.tools;

import com.sun.source.tree.VariableTree;
import kit.edu.translation.core.SafeObservationExpression;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class ObservationJMLTranslator {
    private static List<String> makeJMLComment(List<String> lines) {
        List<String> result = new ArrayList<String>();
        result.add("/*@");
        for (String line : lines) {
            result.add("  @ " + line);
        }
        result.add("  @*/");
        return result;
    }

    private static String getObservedVarList(List<String> vars) {
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
        List<String> observedVars = new ArrayList<String>();
        for (VariableTree var : oexpr.safeVariables) {
            observedVars.add(var.getName().toString());
        }
        if (oexpr.safeResult) {
            observedVars.add("\\result");
        }
        result.append(getObservedVarList(observedVars));
        result.append(" \\by ");
        if (oexpr.safeResult) {
            // \result only appears in the first part of the determines clause
            observedVars.remove(observedVars.size() - 1);
        }
        result.append(getObservedVarList(observedVars));
        result.append(";");
        return result.toString();
    }
    public static List<String> TranslateSafeObservationToJML(SafeObservationExpression safeObservationExpression) {
        return makeJMLComment(Collections.singletonList(getDeterminesClause(safeObservationExpression)));
    }

}
