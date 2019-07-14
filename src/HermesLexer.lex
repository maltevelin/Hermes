{
 open Lexing;

 exception LexicalError of string * (int * int) (* (message, (line, column)) *)

 val currentLine = ref 1
 val lineStartPos = ref [0]

 fun getPos lexbuf = getLineCol (getLexemeStart lexbuf)
				(!currentLine)
				(!lineStartPos)

 and getLineCol pos line (p1::ps) =
       if pos>=p1 then (line, pos-p1)
       else getLineCol pos (line-1) ps
   | getLineCol pos line [] = raise LexicalError ("",(0,0))

 fun lexerError lexbuf s = 
     raise LexicalError (s, getPos lexbuf)

 fun keyword (s, pos) =
     case s of
         "call"         => HermesParser.CALL pos
       | "uncall"       => HermesParser.UNCALL pos
       | "scanf"        => HermesParser.SCANF pos
       | "printf"       => HermesParser.PRINTF pos
       | "if"           => HermesParser.IF pos
       | "fi"           => HermesParser.FI pos
       | "else"         => HermesParser.ELSE pos
       | "from"         => HermesParser.FROM pos
       | "loop"         => HermesParser.LOOP pos
       | "until"        => HermesParser.UNTIL pos
       | "do"           => HermesParser.DO pos
       | "while"        => HermesParser.WHILE pos
       | "for"          => HermesParser.FOR pos
       | "assert"       => HermesParser.ASSERT pos
       | "i8"           => HermesParser.I8 pos
       | "u8"           => HermesParser.U8 pos
       | "i16"          => HermesParser.I16 pos
       | "u16"          => HermesParser.U16 pos
       | "i32"          => HermesParser.I32 pos
       | "u32"          => HermesParser.U32 pos
       | "i64"          => HermesParser.I64 pos
       | "u64"          => HermesParser.U64 pos
       | "const"        => HermesParser.CONST pos
       | _              => HermesParser.ID (s, pos)

 }

rule Token = parse
    [` ` `\t` `\r`]+    { Token lexbuf } (* whitespace *)
    | "//" [^`\n`]*	{ Token lexbuf } (* comment *)
    | "/*" ([^`*`] | `*`[^`/`])* "*/"
		 	{ Token lexbuf } (* comment *)
  | [`\n` `\012`]       { currentLine := !currentLine+1;
                          lineStartPos :=  getLexemeStart lexbuf
			                   :: !lineStartPos;
                          Token lexbuf } (* newlines *)
  | [`0`-`9`]+          { HermesParser.NUM (getLexeme lexbuf, getPos lexbuf) }
  | "0x"[`0`-`9` `A`-`F` `a`-`f`]+
                        { HermesParser.NUM (getLexeme lexbuf, getPos lexbuf) }
  | [`a`-`z``A`-`Z`] [`a`-`z``A`-`Z``0`-`9``_`]*
                        { keyword (getLexeme lexbuf,getPos lexbuf) }
  | `"` ([` ` `!` `#`-`&` `(`-`[` `]`-`~`] | `\`[` `-`~`])* `"`
                        { HermesParser.STRINGCONST
                            (case String.fromCString (getLexeme lexbuf) of
                               NONE => lexerError lexbuf "Bad string constant"
                             | SOME s => String.substring(s,1,
                                                          String.size s - 2),
			    getPos lexbuf) }

  | `+`                 { HermesParser.PLUS (getPos lexbuf) }
  | `-`                 { HermesParser.MINUS (getPos lexbuf) }
  | `*`                 { HermesParser.TIMES (getPos lexbuf) }
  | `/`                 { HermesParser.DIVIDE (getPos lexbuf) }
  | `%`                 { HermesParser.MODULO (getPos lexbuf) }
  | `^`                 { HermesParser.XOR (getPos lexbuf) }
  | `&`                 { HermesParser.BAND (getPos lexbuf) }
  | `|`                 { HermesParser.BOR (getPos lexbuf) }
  | "<<"                { HermesParser.SHIFTL (getPos lexbuf) }
  | ">>"                { HermesParser.SHIFTR (getPos lexbuf) }
  | "++"                { HermesParser.INC (getPos lexbuf) }
  | "--"                { HermesParser.DEC (getPos lexbuf) }
  | "+="                { HermesParser.ADD (getPos lexbuf) }
  | "-="                { HermesParser.SUB (getPos lexbuf) }
  | "^="                { HermesParser.XORWITH (getPos lexbuf) }
  | "<<="               { HermesParser.ROL (getPos lexbuf) }
  | ">>="               { HermesParser.ROR (getPos lexbuf) }
  | "="                 { HermesParser.EQ (getPos lexbuf) }
  | "=="                { HermesParser.EQUAL (getPos lexbuf) }
  | `<`                 { HermesParser.LESS (getPos lexbuf) }
  | `>`                 { HermesParser.GREATER (getPos lexbuf) }
  | "!="                { HermesParser.NEQ (getPos lexbuf) }
  | "<="                { HermesParser.LEQ (getPos lexbuf) }
  | ">="                { HermesParser.GEQ (getPos lexbuf) }
  | "~"                 { HermesParser.BNOT (getPos lexbuf) }
  | "<->"               { HermesParser.SWAP (getPos lexbuf) }
  | `[`                 { HermesParser.LBRACK (getPos lexbuf) }
  | `]`                 { HermesParser.RBRACK (getPos lexbuf) }
  | `{`                 { HermesParser.LBRACE (getPos lexbuf) }
  | `}`                 { HermesParser.RBRACE (getPos lexbuf) }
  | `(`                 { HermesParser.LPAR (getPos lexbuf) }
  | `)`                 { HermesParser.RPAR (getPos lexbuf) }
  | `;`                 { HermesParser.SEMICOLON (getPos lexbuf) }
  | `,`                 { HermesParser.COMMA (getPos lexbuf) }
  | eof                 { HermesParser.EOF (getPos lexbuf) }
  | _                   { lexerError lexbuf "Illegal symbol in input" }

;
