import tlc2.value.impl.IntValue;

// Compiled with javac --release 8 -cp tla2tools.jar Ext.java
public class Ext {
    public static IntValue Op(IntValue x) {
        return IntValue.gen(x.val + 100);
    }
}
