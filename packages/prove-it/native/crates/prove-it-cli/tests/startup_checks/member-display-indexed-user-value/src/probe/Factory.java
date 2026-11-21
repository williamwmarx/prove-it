package probe; import tlc2.value.impl.*; import tlc2.overrides.TLAPlusOperator;
public class Factory {
 @TLAPlusOperator(identifier=":>",module="TLC",warn=false)
 public static Value replace(Value key,Value val){return new UserValue(new UserObj(){
 public int compareTo(Value value){return 0;}
 public boolean member(Value value){return false;}
 public boolean isFinite(){return true;}
 public boolean isEmpty(){return false;}
 public StringBuffer toString(StringBuffer b,int o,boolean s){return b.append("<<{1, \"a\"}>>");}
 });}
}