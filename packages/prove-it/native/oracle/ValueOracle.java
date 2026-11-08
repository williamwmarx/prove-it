// Answers questions about values with TLC's own Value classes, for scripts/value-oracle.ts
// (DESIGN.md 6.8). It reads one request a line and writes one answer a line:
//
//   strings <text>...       interns the texts in order, as TLC interns a spec's strings, and
//                           answers "tokens" and each text's UniqueString token
//   value <tokens>          builds and normalizes a value, numbered from 0 in the order built,
//                           and answers "ok"
//   compare <i> <j>         answers the sign of compareTo
//   equals <i> <j>          answers true or false
//   member <i> <j>          answers whether value i is an element of set j
//   fingerprint <i>         answers fingerPrint(FP64.New()) as a signed decimal
//   enumerate <q|s> <i>     answers "elements" and the fingerprint of each element of set i, in
//                           the order a quantifier binds them (q, Ordering.NORMALIZED) or the
//                           order x' \in S assigns them (s, elements())
//
// A request TLC fails on answers "!" and the exception's class. A value is written as prefix
// tokens: T and F, i<int>, s<text> for a string and m<text> for a model value, S<n> for a set of
// the n values that follow, U<n> for a tuple, R<n> for a record of n field names (as s tokens) and
// values, and f<n> for a function of n keys and values. A text is its UTF-16 code units in hex,
// four digits each. The sets TLC keeps lazy are built as Tool builds them: Lp for SUBSET of the
// value that follows, Lf for [D -> R] of the two, Lr<n> for a set of records of n field names (as
// s tokens) and sets, Lx<n> for the product of n sets, and Lu, Li and Ld for the union,
// intersection and difference of two, which a set enumeration combines with the other set itself.
// Usage: javac -cp tla2tools.jar ValueOracle.java && java -cp tla2tools.jar:. ValueOracle

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;

import tlc2.util.FP64;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.Enumerable;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.ModelValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.Reducible;
import tlc2.value.impl.SetCapValue;
import tlc2.value.impl.SetCupValue;
import tlc2.value.impl.SetDiffValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.SetOfFcnsValue;
import tlc2.value.impl.SetOfRcdsValue;
import tlc2.value.impl.SetOfTuplesValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.SubsetValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;
import tlc2.value.impl.ValueEnumeration;
import util.UniqueString;

public final class ValueOracle {
  private final List<Value> values = new ArrayList<>();
  private String[] tokens;
  private int next;

  private static String decode(String hex) {
    final StringBuilder text = new StringBuilder();
    for (int index = 0; index < hex.length(); index += 4) {
      text.append((char) Integer.parseInt(hex.substring(index, index + 4), 16));
    }
    return text.toString();
  }

  private Value[] read(int count) {
    final Value[] read = new Value[count];
    for (int index = 0; index < count; index++) read[index] = read();
    return read;
  }

  private Value read() {
    final String token = tokens[next++];
    final String rest = token.substring(1);
    switch (token.charAt(0)) {
      case 'T':
        return BoolValue.ValTrue;
      case 'F':
        return BoolValue.ValFalse;
      case 'i':
        return IntValue.gen(Integer.parseInt(rest));
      case 's':
        return new StringValue(decode(rest));
      case 'm':
        return (Value) ModelValue.make(decode(rest));
      case 'S':
        return (Value) new SetEnumValue(read(Integer.parseInt(rest)), false).normalize();
      case 'U':
        return new TupleValue(read(Integer.parseInt(rest)));
      case 'R': {
        final int size = Integer.parseInt(rest);
        final UniqueString[] names = new UniqueString[size];
        final Value[] fields = new Value[size];
        for (int index = 0; index < size; index++) {
          names[index] = UniqueString.uniqueStringOf(decode(tokens[next++].substring(1)));
          fields[index] = read();
        }
        return (Value) new RecordValue(names, fields, false).normalize();
      }
      case 'f': {
        final int size = Integer.parseInt(rest);
        final Value[] domain = new Value[size];
        final Value[] range = new Value[size];
        for (int index = 0; index < size; index++) {
          domain[index] = read();
          range[index] = read();
        }
        return (Value) new FcnRcdValue(domain, range, false).normalize();
      }
      case 'L':
        return readLazy(rest);
      default:
        throw new IllegalArgumentException("unknown token " + token);
    }
  }

  // A set TLC keeps lazy, as Tool.evalAppl builds it.
  private Value readLazy(String kind) {
    switch (kind.charAt(0)) {
      case 'p':
        return new SubsetValue(read());
      case 'f': {
        final Value domain = read();
        return new SetOfFcnsValue(domain, read());
      }
      case 'r': {
        final int size = Integer.parseInt(kind.substring(1));
        final UniqueString[] names = new UniqueString[size];
        final Value[] sets = new Value[size];
        for (int index = 0; index < size; index++) {
          names[index] = UniqueString.uniqueStringOf(decode(tokens[next++].substring(1)));
          sets[index] = read();
        }
        return new SetOfRcdsValue(names, sets, false);
      }
      case 'x':
        return new SetOfTuplesValue(read(Integer.parseInt(kind.substring(1))));
      case 'u': {
        final Value left = read();
        final Value right = read();
        if (left instanceof Reducible) return ((Reducible) left).cup(right);
        if (right instanceof Reducible) return ((Reducible) right).cup(left);
        return new SetCupValue(left, right);
      }
      case 'i': {
        final Value left = read();
        final Value right = read();
        if (left instanceof Reducible) return ((Reducible) left).cap(right);
        if (right instanceof Reducible) return ((Reducible) right).cap(left);
        return new SetCapValue(left, right);
      }
      case 'd': {
        final Value left = read();
        final Value right = read();
        if (left instanceof Reducible) return ((Reducible) left).diff(right);
        return new SetDiffValue(left, right);
      }
      default:
        throw new IllegalArgumentException("unknown lazy set L" + kind);
    }
  }

  private String enumerate(String order, Value set) {
    final ValueEnumeration elements =
        order.equals("q")
            ? ((Enumerable) set).elements(Enumerable.Ordering.NORMALIZED)
            : ((Enumerable) set).elements();
    final StringBuilder answer = new StringBuilder("elements");
    for (Value element = elements.nextElement();
        element != null;
        element = elements.nextElement()) {
      answer.append(' ').append(element.fingerPrint(FP64.New()));
    }
    return answer.toString();
  }

  private Value get(int index) {
    return values.get(Integer.parseInt(tokens[index]));
  }

  private String answer(String line) {
    tokens = line.split(" ");
    next = 1;
    switch (tokens[0]) {
      case "strings": {
        final StringBuilder answer = new StringBuilder("tokens");
        for (int index = 1; index < tokens.length; index++) {
          final String text = decode(tokens[index].substring(1));
          answer.append(' ').append(UniqueString.uniqueStringOf(text).getTok());
        }
        return answer.toString();
      }
      case "value": {
        // A value TLC fails to build still takes its number, so the numbers stay in step.
        values.add(null);
        values.set(values.size() - 1, read());
        return "ok";
      }
      case "compare":
        return Integer.toString(Integer.signum(get(1).compareTo(get(2))));
      case "equals":
        return Boolean.toString(get(1).equals(get(2)));
      case "member":
        return Boolean.toString(get(2).member(get(1)));
      case "fingerprint":
        return Long.toString(get(1).fingerPrint(FP64.New()));
      case "enumerate":
        return enumerate(tokens[1], get(2));
      default:
        throw new IllegalArgumentException("unknown request " + tokens[0]);
    }
  }

  public static void main(String[] args) throws Exception {
    FP64.Init(0);
    final ValueOracle oracle = new ValueOracle();
    final BufferedReader input =
        new BufferedReader(new InputStreamReader(System.in, StandardCharsets.UTF_8));
    final PrintStream output = new PrintStream(System.out, false, StandardCharsets.UTF_8);
    for (String line = input.readLine(); line != null; line = input.readLine()) {
      String answer;
      try {
        answer = oracle.answer(line);
      } catch (Throwable thrown) {
        answer = "!" + thrown.getClass().getSimpleName();
      }
      output.println(answer);
    }
    output.flush();
  }
}
