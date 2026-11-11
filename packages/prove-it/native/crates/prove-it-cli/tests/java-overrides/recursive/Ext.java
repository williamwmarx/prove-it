import tlc2.value.impl.IntValue;
import tlc2.value.impl.Value;

// Compiled with javac --release 8 -cp tla2tools.jar Ext.java
public class Ext {
    public static Value Op() {
        return IntValue.gen(101);
    }
}
