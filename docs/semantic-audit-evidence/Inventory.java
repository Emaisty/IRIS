import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.Interval;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.TerminalNode;
import org.arend.frontend.parser.ArendLexer;
import org.arend.frontend.parser.ArendParser;
import com.sun.source.tree.*;
import com.sun.source.util.*;
import javax.tools.*;
import java.nio.file.*;
import java.util.*;

/** Grammar-backed inventory, including private/nested declarations, constructors,
 * class fields, aliases, and named let-bindings. No elaboration or cache access. */
public class Inventory {
  static String file;
  static CharStream input;
  static int errors;
  static String quote(String s) {
    return "\"" + s.replace("\\", "\\\\").replace("\"", "\\\"")
      .replace("\n", "\\n").replace("\r", "\\r").replace("\t", "\\t") + "\"";
  }
  static void emit(String kind, String name, String owner, int line, int end,
                   String signature, String access) {
    System.out.println("{\"file\":"+quote(file)+",\"kind\":"+quote(kind)+",\"name\":"+quote(name)
      +",\"owner\":"+quote(owner)+",\"line\":"+line+",\"end_line\":"+end
      +",\"access\":"+quote(access)+",\"signature\":"+quote(signature)+"}");
  }
  static String access(ParseTree p) {
    for (; p != null; p = p.getParent()) {
      if (p instanceof ArendParser.AccessModContext) return p.getText();
      if (p instanceof ArendParser.StatDefContext c && c.accessMod() != null) return c.accessMod().getText();
      if (p instanceof ArendParser.StatAccessModContext c) return c.accessMod().getText();
      if (p instanceof ArendParser.ClassFieldDefContext c && c.accessMod() != null) return c.accessMod().getText();
    }
    return "default";
  }
  static void walk(ParseTree t, String owner) {
    String name = null, kind = null;
    ParserRuleContext body = null;
    ArendParser.DefIdContext id = null;
    if (t instanceof ArendParser.DefFunctionContext c) {
      kind = c.funcKw().getText(); id = c.topDefId().defId(); body = c.functionBody();
    } else if (t instanceof ArendParser.DefDataContext c) {
      kind = "\\data"; id = c.topDefId().defId(); body = c.dataBody();
    } else if (t instanceof ArendParser.DefClassContext c) {
      kind = c.classKw().getText(); id = c.topDefId().defId(); body = c.classBody();
    } else if (t instanceof ArendParser.DefInstanceContext c) {
      kind = c.instanceKw().getText(); id = c.topDefId().defId(); body = c.instanceBody();
    } else if (t instanceof ArendParser.DefModuleContext c) {
      kind = "\\module"; name = c.ID().getText(); body = c.where();
    } else if (t instanceof ArendParser.DefMetaContext c) {
      kind = "\\meta"; id = c.defId(); body = c.where();
    } else if (t instanceof ArendParser.ConstructorContext c) {
      kind = "constructor"; id = c.defId();
    } else if (t instanceof ArendParser.ClassFieldDefContext c) {
      kind = "field"; id = c.defId();
    } else if (t instanceof ArendParser.LetClauseContext c) {
      kind = "local-binding"; name = c.ID() == null ? c.atomPattern().getText() : c.ID().getText(); body = c.expr();
    }
    if (id != null) name = id.ID().getText();
    if (name != null) {
      ParserRuleContext c = (ParserRuleContext)t;
      int stop = body == null ? c.stop.getStopIndex() : body.start.getStartIndex()-1;
      emit(kind, name, owner, c.start.getLine(), c.stop.getLine(),
           input.getText(Interval.of(c.start.getStartIndex(), Math.max(c.start.getStartIndex(), stop))), access(t));
      if (id != null && id.alias() != null) {
        emit("alias", id.alias().ID().getText(), owner, id.alias().start.getLine(), id.alias().stop.getLine(), name, access(t));
      }
      if (!kind.equals("local-binding")) owner = owner.isEmpty() ? name : owner + "." + name;
    }
    if (t instanceof ArendParser.FieldTeleContext c) {
      for (int i=0; i<c.getChildCount(); i++) {
        if (c.getChild(i) instanceof TerminalNode n && n.getSymbol().getType() == ArendLexer.ID) {
          emit("parameter-field", n.getText(), owner, n.getSymbol().getLine(), c.stop.getLine(),
               input.getText(Interval.of(c.start.getStartIndex(), c.stop.getStopIndex())), access(t));
        }
      }
    }
    for (int i=0; i<t.getChildCount(); i++) walk(t.getChild(i), owner);
  }
  static void arend(Path p) throws Exception {
    input = CharStreams.fromPath(p);
    ArendLexer lexer = new ArendLexer(input);
    ArendParser parser = new ArendParser(new CommonTokenStream(lexer));
    BaseErrorListener listener = new BaseErrorListener() {
      public void syntaxError(Recognizer<?,?> r, Object bad, int line, int col, String msg, RecognitionException e) {
        errors++; System.err.println(file+":"+line+":"+col+": "+msg);
      }
    };
    lexer.removeErrorListeners(); lexer.addErrorListener(listener);
    parser.removeErrorListeners(); parser.addErrorListener(listener);
    walk(parser.statements(), "");
  }
  static void java(Path p) throws Exception {
    JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();
    try (StandardJavaFileManager fm = compiler.getStandardFileManager(null, null, null)) {
      JavacTask task = (JavacTask)compiler.getTask(null, fm, d -> {
        if (d.getKind() == Diagnostic.Kind.ERROR) { errors++; System.err.println(d); }
      }, List.of("-proc:none"), null, fm.getJavaFileObjects(p.toFile()));
      String source = Files.readString(p);
      Trees trees = Trees.instance(task);
      for (CompilationUnitTree unit : task.parse()) {
        SourcePositions pos = trees.getSourcePositions();
        new TreePathScanner<Void,String>() {
          void entry(Tree t, String kind, String name, String owner, int boundary, String access) {
            int start = (int)pos.getStartPosition(unit,t), end = (int)pos.getEndPosition(unit,t);
            if (start < 0 || end < 0) return;
            emit(kind,name,owner,(int)unit.getLineMap().getLineNumber(start),
                 (int)unit.getLineMap().getLineNumber(end-1), source.substring(start,boundary<0?end:boundary), access);
          }
          public Void visitClass(ClassTree t,String owner) {
            entry(t,"java-class",t.getSimpleName().toString(),owner,
                  source.indexOf('{',(int)pos.getStartPosition(unit,t)),t.getModifiers().toString());
            return super.visitClass(t,owner.isEmpty()?t.getSimpleName().toString():owner+"."+t.getSimpleName());
          }
          public Void visitMethod(MethodTree t,String owner) {
            entry(t,"java-method",t.getName().toString(),owner,
                  t.getBody()==null?-1:(int)pos.getStartPosition(unit,t.getBody()),t.getModifiers().toString());
            return super.visitMethod(t,owner+"."+t.getName());
          }
          public Void visitVariable(VariableTree t,String owner) {
            if (getCurrentPath().getParentPath().getLeaf() instanceof ClassTree)
              entry(t,"java-field",t.getName().toString(),owner,-1,t.getModifiers().toString());
            return super.visitVariable(t,owner);
          }
        }.scan(unit, "");
      }
    }
  }
  public static void main(String[] args) throws Exception {
    Path root = Path.of(args[0]);
    for (String path : Files.readAllLines(Path.of(args[1]))) {
      file = path;
      if (path.endsWith(".ard")) arend(root.resolve(path));
      if (path.endsWith(".java")) java(root.resolve(path));
    }
    System.err.println("parse_errors="+errors);
    if (errors != 0) System.exit(1);
  }
}
