import checkers.inference.sflow.quals.*;

class TestProgram {
  public static class A {
    public @Safe int safe;
    public @Tainted int tainted;

    @TaintedMethod
    public void foo() {}

    public void error() {
      if (tainted == 0) {
        foo();
      }
    }
  }

  public static class B extends A {
    @TaintedMethod
    public void foo() {
      safe = 0;
    }
  }
}
