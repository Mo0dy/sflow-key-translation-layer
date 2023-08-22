import java.util.*;

import checkers.inference.sflow.quals.*;

class TestProgram extends TestParent {
    public @Tainted int class_tainted;
    public @Safe int class_safe;
    public void test3() {
        safe_var_parent = class_tainted;
    }
}
