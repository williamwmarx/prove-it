import tlc2.value.impl.*;
public class Json { public static Value ToJsonArray(Value v) { return new StringValue("external-array"); } public static Value ToJsonObject(Value v) { return new StringValue("external-object"); } }
