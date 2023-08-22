import java.util.*;

class TestProgram {
    public @Tainted int class_tainted;
    public @Tainted int[] class_tainted_arr;
    public @Safe int class_safe;

    public void testThrow() {
        if (class_tainted > 0) {
            throw new RuntimeException();
        }
    }

    public void testContinue() {
        for (@Safe
        int i = 0; i < 10; i++) {
            if (class_tainted > 0) {
                continue;
            }
            class_safe = 0;
        }
    }

    public void testBreak() {
        for (@Safe
        int i = 0; i < 10; i++) {
            if (class_tainted > 0) {
                break;
            }
            class_safe = 0;
        }
    }

    public void testCaseBreak() {
        switch (0) {
            case 0:
                if (class_tainted > 0) {
                    break;
                }
                class_safe = 0;
                break;
        }
    }

    public void testIf() {
        if (class_tainted > 0) {
            class_safe = 0;
        }
    }

    public void testElse() {
        if (class_tainted > 0) {
            class_tainted = 0;
        } else {
            class_safe = 0;
        }
    }

    public void testElseIf() {
        if (class_tainted > 0) {
            class_tainted = 0;
        } else if (class_tainted < 0) {
            class_safe = 0;
        }
    }

    public void testWhile() {
        int i = 0;
        while (i < class_tainted) {
            class_safe = 0;
            i++;
        }
    }

    public void testDoWhile() {
        int i = 0;
        do {
            class_safe = 0;
            i++;
        } while (i < class_tainted);
    }

    public void testForAssign() {
        @Safe
        int j = 0;
        for (int i = class_tainted; i < 10; i++) {
            class_safe = 0;
        }
    }

    public void testForCond() {
        for (int i = 0; i < class_tainted; i++) {
            class_safe = 0;
        }
    }

    public void testForIncr() {
        for (int i = 0; i < 10; i += class_tainted) {
            class_safe = 0;
        }
    }

    public void testForIncr2() {
        for (int i = 0; i < class_tainted; class_safe = 0) {
            i++;
        }
    }

    public void testEnhancedFor() {
        for (int i : class_tainted_arr) {
            class_safe = 0;
        }
    }

    public void testSwitch() {
        switch (class_tainted) {
            case 0:
                class_safe = 0;
                break;
        }
    }
}
