import java.util.*;

import checkers.inference.sflow.quals.*;

class TestProgram {
    private @Tainted int class_tainted;
    private @Safe int class_safe;

    public static void main(String[] args) {
        TestClass tc = new TestClass();
        tc.test();
        int x = 0;
        int y = 1;
        y = x;
        x = y;
        test1(x, y);
    }

    public static void test1(@Safe int a1, @Safe int a2) {
        System.out.println(a2);
    }

    public static @Tainted String test2(@Safe String a1, @Safe String a2) {
        return a2;
    }

    public void test3() {
        class_safe = class_tainted;
    }
}
