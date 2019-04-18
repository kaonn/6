type pos = string -> Coord.t
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue, pos) token
type arg = string

val pos = ref Coord.init
val eof = fn (fileName : string) => Tokens.EOF (!pos, !pos)

exception LexerError of pos

%%
%arg (fileName : string);
%header (functor ExampleLexFun (structure Tokens : Example_TOKENS));
%s COMMENT;
alpha = [A-Za-z];
digit = [0-9];
any = [@a-zA-Z0-9\'];
whitespace = [\ \t];
%%

<INITIAL>"/*" => (YYBEGIN COMMENT; continue ());
<COMMENT>"*/" => (YYBEGIN INITIAL; continue());
<COMMENT>. => (continue ());

\n                 => (pos := (Coord.nextline o (!pos)); continue ());
{whitespace}+      => (pos := (Coord.addchar (size yytext) o (!pos)); continue ());
{digit}+           => (Tokens.NUMERAL (valOf (Int.fromString yytext), !pos, Coord.addchar (size yytext) o (!pos)));
<INITIAL>"//"[^\n]*         => (continue ());



<INITIAL>"("                => (Tokens.LPAREN (!pos, Coord.nextchar o (!pos)));
<INITIAL>")"                => (Tokens.RPAREN (!pos, Coord.nextchar o (!pos)));
<INITIAL>"{"                => (Tokens.LBRACE (!pos, Coord.nextchar o (!pos)));
<INITIAL>"}"                => (Tokens.RBRACE (!pos, Coord.nextchar o (!pos)));
<INITIAL>"."                => (Tokens.DOT (!pos, Coord.nextchar o (!pos)));
<INITIAL>","                => (Tokens.COMMA (!pos, Coord.nextchar o (!pos)));
<INITIAL>";"                => (Tokens.SEMI (!pos, Coord.nextchar o (!pos)));
<INITIAL>":"                => (Tokens.COLON (!pos, Coord.nextchar o (!pos)));
<INITIAL>"="                => (Tokens.EQUAL (!pos, Coord.nextchar o (!pos)));
<INITIAL>"+"                => (Tokens.PLUS (!pos, Coord.nextchar o (!pos)));
<INITIAL>"-"                => (Tokens.MINUS (!pos, Coord.nextchar o (!pos)));
<INITIAL>">"                => (Tokens.GT (!pos, Coord.nextchar o (!pos)));
<INITIAL>"|"                => (Tokens.MID (!pos, Coord.nextchar o (!pos)));
<INITIAL>"#"                => (Tokens.HASH (!pos, Coord.nextchar o (!pos)));
<INITIAL>"\\"                => (Tokens.LAMBDA (!pos, Coord.nextchar o (!pos)));
<INITIAL>"thunk"             => (Tokens.THUNK (!pos, Coord.addchar 5 o (!pos)));
<INITIAL>"ret"             => (Tokens.RET (!pos, Coord.addchar 3 o (!pos)));
<INITIAL>"rec"             => (Tokens.REC (!pos, Coord.addchar 3 o (!pos)));
<INITIAL>"if"             => (Tokens.IF (!pos, Coord.addchar 2 o (!pos)));
<INITIAL>"then"             => (Tokens.THEN (!pos, Coord.addchar 2 o (!pos)));
<INITIAL>"else"             => (Tokens.ELSE (!pos, Coord.addchar 2 o (!pos)));
<INITIAL>"seq"             => (Tokens.SEQ (!pos, Coord.addchar 3 o (!pos)));
<INITIAL>"zero"             => (Tokens.ZERO (!pos, Coord.addchar 4 o (!pos)));
<INITIAL>"suc"             => (Tokens.SUC (!pos, Coord.addchar 3 o (!pos)));
<INITIAL>"fst"             => (Tokens.FST (!pos, Coord.addchar 3 o (!pos)));
<INITIAL>"snd"             => (Tokens.SND (!pos, Coord.addchar 3 o (!pos)));
<INITIAL>"leaf"             => (Tokens.LEAF (!pos, Coord.addchar 4 o (!pos)));
<INITIAL>"single"             => (Tokens.SINGLE (!pos, Coord.addchar 6 o (!pos)));
<INITIAL>"t2"             => (Tokens.T2 (!pos, Coord.addchar 2 o (!pos)));
<INITIAL>"t3"             => (Tokens.T3 (!pos, Coord.addchar 2 o (!pos)));
<INITIAL>"trec"             => (Tokens.TREC (!pos, Coord.addchar 4 o (!pos)));
<INITIAL>"tmatch"             => (Tokens.TMATCH (!pos, Coord.addchar 6 o (!pos)));
<INITIAL>"<-"              => (Tokens.LARR (!pos, Coord.addchar 2 o (!pos)));

<INITIAL>{alpha}{any}*      => (Tokens.IDENT (yytext, !pos, Coord.addchar (size yytext) o (!pos)));

