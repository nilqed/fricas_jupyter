// CodeMirror, copyright (c) by Marijn Haverbeke and others
// Distributed under an MIT license: http://codemirror.net/LICENSE

(function(mod) {
  if (typeof exports == "object" && typeof module == "object") // CommonJS
    mod(require("../../lib/codemirror"));
  else if (typeof define == "function" && define.amd) // AMD
    define(["../../lib/codemirror"], mod);
  else // Plain browser env
    mod(CodeMirror);
})(function(CodeMirror) {
  "use strict";

  function wordRegexp(words) {
    return new RegExp("^((" + words.join(")|(") + "))\\b");
  }

  var wordOperators = wordRegexp(["and", "or", "not", "is"]);
  var commonKeywords = ["break", "continue",
                        "else", "finally",
                        "for", "from", "global", "if", "import", "in",
                        "repeat", "return", "then", "to",
                        "while"];
  var commonBuiltins = ["abs", "ARRAY1", "Any", "Boolean", "BOOL", "CHAR",
                        "Complex", "COMPLEX", "concat", "elt", "error", "eval", "expand",
                        "false", "Field", "first", "Float", "FLOAT", "Fraction","FRAC",
                        "generate", "has", "hash",
                        "Integer", "IntegerMod", "INT", "len","List",
                        "map", "map!", "max", "min", "next",
                        "new", "NonNegativeInteger",
                        "OneDimensionalArray", "output",
                        "Polynomial", "PositiveInteger", "PrimeField", "print",
                        "Ring", "Record", "rem", "rest", "round",
                        "Set", "Stream", "String", "sum", "Symbol",
                        "true", "Tuple", "TwoDimensionalArray","Type",
                        "Union", "Vector", "vector", "zip",
                        "#", "%e", "%i", "%infinity", "%minusInfinity", "%pi", "%plusInfinity"];

  CodeMirror.registerHelper("hintWords", "spad", commonKeywords.concat(commonBuiltins));

  function top(state) {
    return state.scopes[state.scopes.length - 1];
  }

  CodeMirror.defineMode("spad", function(conf, parserConf) {
    var ERRORCLASS = "error";

    var singleDelimiters = parserConf.singleDelimiters || new RegExp("^[\\(\\)\\[\\]\\{\\},:=;|\\.]");
    var doubleOperators = parserConf.doubleOperators || new RegExp("^((==)|(~=)|(<=)|(>=)|(=>)|(->)|(\\:=)|(\\:\\:)|(\\.\\.))");
    var doubleDelimiters = parserConf.doubleDelimiters || new RegExp("^((\\+=)|(\\-=)|(\\*=)|(%=)|(/=)|(&=)|(\\|=)|(\\^=))");

    var singleOperators = parserConf.singleOperators || new RegExp("^[\\+\\-\\*/%&|\\^~<>@\\$]");
    var identifiers = parserConf.identifiers|| new RegExp("^[_A-Za-z%][_A-Za-z0-9!\\?]*");

    var hangingIndent = parserConf.hangingIndent || conf.indentUnit;

    var myKeywords = commonKeywords, myBuiltins = commonBuiltins;
    if(parserConf.extra_keywords != undefined){
      myKeywords = myKeywords.concat(parserConf.extra_keywords);
    }
    if(parserConf.extra_builtins != undefined){
      myBuiltins = myBuiltins.concat(parserConf.extra_builtins);
    }
    var stringPrefixes = new RegExp("[\"]", "i");
    var keywords = wordRegexp(myKeywords);
    var builtins = wordRegexp(myBuiltins);

    // tokenizers
    function tokenBase(stream, state) {
      // Handle scope changes
      if (stream.sol() && top(state).type == "py") {
        var scopeOffset = top(state).offset;
        if (stream.eatSpace()) {
          var lineOffset = stream.indentation();
          if (lineOffset > scopeOffset)
            pushScope(stream, state, "py");
          else if (lineOffset < scopeOffset && dedent(stream, state))
            state.errorToken = true;
          return null;
        } else {
          var style = tokenBaseInner(stream, state);
          if (scopeOffset > 0 && dedent(stream, state))
            style += " " + ERRORCLASS;
          return style;
        }
      }
      return tokenBaseInner(stream, state);
    }

    function tokenBaseInner(stream, state) {
      if (stream.eatSpace()) return null;

      // Handle Comments
      if (stream.match("--",false) || stream.match("++",false)) {
        stream.skipToEnd();
        return "comment";
      }

      // Handle Number Literals
      if (stream.match(/^[0-9\.]/, false)) {
        var floatLiteral = false;
        // Floats
        if (stream.match(/^\d*\.\d+(E[\+\-]?\d+)?/i)) { floatLiteral = true; }
        if (stream.match(/^\d+\.\d+/)) { floatLiteral = true; }
        if (stream.match(/^\.\d+/)) { floatLiteral = true; }
        if (floatLiteral) {
          return "number";
        }
        // Integers
        var intLiteral = false;
        // Hex
        // Binary
        // Octal
        // Decimal
        if (stream.match(/^[1-9]\d*(e[\+\-]?\d+)?/)) {
          intLiteral = true;
        }
        // Zero by itself with no other piece of number.
        if (stream.match(/^0(?![\dx])/i)) intLiteral = true;
        if (intLiteral) {
          return "number";
        }
      }

      // Handle Strings
      if (stream.match(stringPrefixes)) {
        state.tokenize = tokenStringFactory(stream.current());
        return state.tokenize(stream, state);
      }

      // Handle operators and Delimiters
      if (stream.match(doubleDelimiters))
        return null;

      if (stream.match(doubleOperators) || stream.match(singleOperators))
        return "operator";

      if (stream.match(singleDelimiters))
        return null;

      if (stream.match(keywords) || stream.match(wordOperators))
        return "keyword";

      if (stream.match(builtins))
        return "builtin";

      if (stream.match(/^(self|cls)\b/))
        return "variable-2";

      if (stream.match(identifiers)) {
        if (state.lastToken == "def" || state.lastToken == "class")
          return "def";
        return "variable";
      }

      // Handle non-detected items
      stream.next();
      return ERRORCLASS;
    }

    function tokenStringFactory(delimiter) {
      while ("rub".indexOf(delimiter.charAt(0).toLowerCase()) >= 0)
        delimiter = delimiter.substr(1);

      var singleline = delimiter.length == 1;
      var OUTCLASS = "string";

      function tokenString(stream, state) {
        while (!stream.eol()) {
          stream.eatWhile(/[^"_]/);
          if (stream.eat("_")) {
            stream.next();
            if (singleline && stream.eol())
              return OUTCLASS;
          } else if (stream.match(delimiter)) {
            state.tokenize = tokenBase;
            return OUTCLASS;
          } else {
            stream.eat(/["]/);
          }
        }
        if (singleline) {
          if (parserConf.singleLineStringErrors)
            return ERRORCLASS;
          else
            state.tokenize = tokenBase;
        }
        return OUTCLASS;
      }
      tokenString.isString = true;
      return tokenString;
    }

    function pushScope(stream, state, type) {
      var offset = 0, align = null;
      if (type == "py") {
        while (top(state).type != "py")
          state.scopes.pop();
      }
      offset = top(state).offset + (type == "py" ? conf.indentUnit : hangingIndent);
      if (type != "py" && !stream.match(/^(\s|#.*)*$/, false))
        align = stream.column() + 1;
      state.scopes.push({offset: offset, type: type, align: align});
    }

    function dedent(stream, state) {
      var indented = stream.indentation();
      while (top(state).offset > indented) {
        if (top(state).type != "py") return true;
        state.scopes.pop();
      }
      return top(state).offset != indented;
    }

    function tokenLexer(stream, state) {
      var style = state.tokenize(stream, state);
      var current = stream.current();

      // Handle "." connected identifiers
      if (current == "." && stream.peek()!=".") {
        style = stream.match(identifiers, false) ? null : ERRORCLASS;
        if (style == null && state.lastStyle == "meta") {
          // Apply "meta" style to "." connected identifiers when
          // appropriate.
          style = "meta";
        }
        return style;
      }

      // Handle decorators
      if (current == "@"){
        if(parserConf.version && parseInt(parserConf.version, 10) == 3){
            return stream.match(identifiers, false) ? "meta" : "operator";
        } else {
            return stream.match(identifiers, false) ? "meta" : ERRORCLASS;
        }
      }

      if ((style == "variable" || style == "builtin")
          && state.lastStyle == "meta")
        style = "meta";

      // Handle scope changes.
      if (current == "pass" || current == "return")
        state.dedent += 1;

      if (current == "lambda") state.lambda = true;
      if (current == "then" && !state.lambda && top(state).type == "py")
        pushScope(stream, state, "py");

      var delimiter_index = current.length == 1 ? "[({".indexOf(current) : -1;
      if (delimiter_index != -1)
        pushScope(stream, state, "])}".slice(delimiter_index, delimiter_index+1));

      delimiter_index = "])}".indexOf(current);
      if (delimiter_index != -1) {
        if (top(state).type == current) state.scopes.pop();
        else return ERRORCLASS;
      }
      if (state.dedent > 0 && stream.eol() && top(state).type == "py") {
        if (state.scopes.length > 1) state.scopes.pop();
        state.dedent -= 1;
      }

      return style;
    }

    var external = {
      startState: function(basecolumn) {
        return {
          tokenize: tokenBase,
          scopes: [{offset: basecolumn || 0, type: "py", align: null}],
          lastStyle: null,
          lastToken: null,
          lambda: false,
          dedent: 0
        };
      },

      token: function(stream, state) {
        var addErr = state.errorToken;
        if (addErr) state.errorToken = false;
        var style = tokenLexer(stream, state);

        state.lastStyle = style;

        var current = stream.current();
        if (current && style)
          state.lastToken = current;

        if (stream.eol() && state.lambda)
          state.lambda = false;
        return addErr ? style + " " + ERRORCLASS : style;
      },

      indent: function(state, textAfter) {
        if (state.tokenize != tokenBase)
          return state.tokenize.isString ? CodeMirror.Pass : 0;

        var scope = top(state);
        var closing = textAfter && textAfter.charAt(0) == scope.type;
        if (scope.align != null)
          return scope.align - (closing ? 1 : 0);
        else if (closing && state.scopes.length > 1)
          return state.scopes[state.scopes.length - 2].offset;
        else
          return scope.offset;
      },

      lineComment: "--",
      fold: "indent"
    };
    return external;
  });

  CodeMirror.defineMIME("text/x-spad", "spad");

  var words = function(str) { return str.split(" "); };

  CodeMirror.defineMIME("text/x-spad", {
    name: "spad",
    extra_keywords: words("add enum except "+
                          "Join "+
                          "where with")
  });

});
