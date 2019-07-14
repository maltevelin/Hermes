OBJS=AbSyn Parser Lexer StaticAnalysis Optimizer CodeGen

hc: hc.sml $(OBJS)
	mkdir -p ../bin
	mosmlc -o ../bin/hc hc.sml

AbSyn: Hermes.sml
	mosmlc -c Hermes.sml

Parser : HermesParser.grm Hermes.ui Hermes.uo
	mosmlyac -v HermesParser.grm
	mosmlc -c HermesParser.sig HermesParser.sml

Lexer: HermesLexer.lex
	mosmllex HermesLexer.lex
	mosmlc -c HermesLexer.sml

SymTab : SymTab.sig SymTab.sml
	mosmlc -c SymTab.sig SymTab.sml

StaticAnalysis : SymTab HermesStaticAnalysis.sig HermesStaticAnalysis.sml
	mosmlc -c HermesStaticAnalysis.sig HermesStaticAnalysis.sml

Optimizer : HermesOptimizer.sig HermesOptimizer.sml
	mosmlc -c HermesOptimizer.sig HermesOptimizer.sml

CodeGen : HermesCompiler.sig HermesCompiler.sml
	mosmlc -c HermesCompiler.sig HermesCompiler.sml

clean:
	rm ../bin/hc
	rm HermesLexer.sml 
	rm HermesParser.sig HermesParser.sml 
	rm *.ui *.uo
	rm *.output
