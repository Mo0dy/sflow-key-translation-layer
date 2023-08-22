import java.util.*;

import checkers.inference.sflow.quals.*;

class TestProgram {
    public @Tainted int class_tainted;
    public @Safe int class_safe;

    public void test() {
        if (class_tainted == 0) {
            break_it(); // Need to know if this method assignes to a safe variable
        }
    }

    // This has a type it's safe since it assignes to a safe variable
    public void break_it() {
        class_safe = 0;
    }

    public void test2() {
        if (break_it_2()) {
            class_safe = 0;
        }
    }

    public @Safe boolean break_it_2() {
        // return values "seem" to be checked by commonAssignmentsCheck
        if (class_tainted == 1) {
            return true;
        } else {
            return false;
        }
    }
}
