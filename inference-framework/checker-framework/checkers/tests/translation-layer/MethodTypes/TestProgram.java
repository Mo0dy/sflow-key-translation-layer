import checkers.inference.sflow.quals.*;

class TestProgram {
  public @Tainted int class_tainted;
  public @Safe int class_safe;

  public void should_work() {
    if (class_tainted == 0) {
      write_tainted();
    }
  }

  public void should_fail() {
    if (class_tainted == 0) {
      write_safe();
    }
  }

  @TaintedMethod
  public void write_tainted() {
    class_tainted = 0;
  }

  @SafeMethod
  public void write_safe() {
    class_safe = 0;
  }

  @TaintedMethod
  public void incorrect_tainted_annotation() {
    class_safe = 0;
  }

  @SafeMethod
  public void correct_safe_annotation() {
    class_tainted = 0;
  }
}
