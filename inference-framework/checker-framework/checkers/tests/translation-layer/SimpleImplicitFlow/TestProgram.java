import java.util.*;

import checkers.inference.sflow.quals.*;

class TestProgram {
    public @Tainted int class_tainted;
    public @Safe int class_safe;
    public void test() {
        if (class_tainted == 0) {
            class_safe = 0;
        }
    }
}
