/* A Bison parser, made by GNU Bison 2.3.  */

/* Skeleton interface for Bison's Yacc-like parsers in C

   Copyright (C) 1984, 1989, 1990, 2000, 2001, 2002, 2003, 2004, 2005, 2006
   Free Software Foundation, Inc.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2, or (at your option)
   any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 51 Franklin Street, Fifth Floor,
   Boston, MA 02110-1301, USA.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* Tokens.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
   /* Put the tokens into the symbol table, so that GDB and other debuggers
      know about them.  */
   enum yytokentype {
     RESET = 258,
     EVAL = 259,
     STEP = 260,
     LET = 261,
     GOTO = 262,
     MAXU = 263,
     MINU = 264,
     ABU = 265,
     EBU = 266,
     AU = 267,
     EU = 268,
     CONTEXT = 269,
     LAMBDA = 270,
     MODTYPE = 271,
     PROCESS = 272,
     MODULE = 273,
     ASYNC = 274,
     ASSIGN = 275,
     CONSTANT = 276,
     ISA = 277,
     FAIRNESS = 278,
     COMPUTE = 279,
     SPEC = 280,
     PRINT = 281,
     FORMAT = 282,
     INVAR = 283,
     TRANS = 284,
     INIT = 285,
     DEFINE = 286,
     VAR = 287,
     EXPOSE = 288,
     HIDE = 289,
     IMPLEMENTS = 290,
     OUTPUT = 291,
     INPUT = 292,
     BDD = 293,
     OVER = 294,
     LIST = 295,
     SCALAR = 296,
     OF = 297,
     ARRAY = 298,
     BOOLEAN = 299,
     RCB = 300,
     LCB = 301,
     RB = 302,
     LB = 303,
     RP = 304,
     LP = 305,
     SEMI = 306,
     ATLINE = 307,
     TWODOTS = 308,
     EQDEF = 309,
     TRUEEXP = 310,
     FALSEEXP = 311,
     SIGMA = 312,
     SELF = 313,
     APROPOS = 314,
     COLON = 315,
     ESAC = 316,
     CASE = 317,
     ATOM = 318,
     NUMBER = 319,
     QUOTE = 320,
     COMMA = 321,
     IMPLIES = 322,
     IFF = 323,
     OR = 324,
     AND = 325,
     NOT = 326,
     MAX = 327,
     MIN = 328,
     BUNTIL = 329,
     ABG = 330,
     ABF = 331,
     EBG = 332,
     EBF = 333,
     UNTIL = 334,
     A = 335,
     E = 336,
     AG = 337,
     EG = 338,
     AF = 339,
     EF = 340,
     AX = 341,
     EX = 342,
     EPATH = 343,
     APATH = 344,
     GE = 345,
     LE = 346,
     GT = 347,
     LT = 348,
     NOTEQUAL = 349,
     EQUAL = 350,
     UNION = 351,
     SETNOTIN = 352,
     SETIN = 353,
     MOD = 354,
     MINUS = 355,
     PLUS = 356,
     DIVIDE = 357,
     TIMES = 358,
     UMINUS = 359,
     SMALLINIT = 360,
     NEXT = 361,
     DOT = 362
   };
#endif
/* Tokens.  */
#define RESET 258
#define EVAL 259
#define STEP 260
#define LET 261
#define GOTO 262
#define MAXU 263
#define MINU 264
#define ABU 265
#define EBU 266
#define AU 267
#define EU 268
#define CONTEXT 269
#define LAMBDA 270
#define MODTYPE 271
#define PROCESS 272
#define MODULE 273
#define ASYNC 274
#define ASSIGN 275
#define CONSTANT 276
#define ISA 277
#define FAIRNESS 278
#define COMPUTE 279
#define SPEC 280
#define PRINT 281
#define FORMAT 282
#define INVAR 283
#define TRANS 284
#define INIT 285
#define DEFINE 286
#define VAR 287
#define EXPOSE 288
#define HIDE 289
#define IMPLEMENTS 290
#define OUTPUT 291
#define INPUT 292
#define BDD 293
#define OVER 294
#define LIST 295
#define SCALAR 296
#define OF 297
#define ARRAY 298
#define BOOLEAN 299
#define RCB 300
#define LCB 301
#define RB 302
#define LB 303
#define RP 304
#define LP 305
#define SEMI 306
#define ATLINE 307
#define TWODOTS 308
#define EQDEF 309
#define TRUEEXP 310
#define FALSEEXP 311
#define SIGMA 312
#define SELF 313
#define APROPOS 314
#define COLON 315
#define ESAC 316
#define CASE 317
#define ATOM 318
#define NUMBER 319
#define QUOTE 320
#define COMMA 321
#define IMPLIES 322
#define IFF 323
#define OR 324
#define AND 325
#define NOT 326
#define MAX 327
#define MIN 328
#define BUNTIL 329
#define ABG 330
#define ABF 331
#define EBG 332
#define EBF 333
#define UNTIL 334
#define A 335
#define E 336
#define AG 337
#define EG 338
#define AF 339
#define EF 340
#define AX 341
#define EX 342
#define EPATH 343
#define APATH 344
#define GE 345
#define LE 346
#define GT 347
#define LT 348
#define NOTEQUAL 349
#define EQUAL 350
#define UNION 351
#define SETNOTIN 352
#define SETIN 353
#define MOD 354
#define MINUS 355
#define PLUS 356
#define DIVIDE 357
#define TIMES 358
#define UMINUS 359
#define SMALLINIT 360
#define NEXT 361
#define DOT 362




#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE
#line 16 "grammar.y"
{
  node_ptr node;
}
/* Line 1529 of yacc.c.  */
#line 267 "y.tab.h"
	YYSTYPE;
# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
# define YYSTYPE_IS_TRIVIAL 1
#endif

extern YYSTYPE yylval;

