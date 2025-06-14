/* A Bison parser, made by GNU Bison 2.3.  */

/* Skeleton implementation for Bison's Yacc-like parsers in C

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

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Bison version.  */
#define YYBISON_VERSION "2.3"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 0

/* Using locations.  */
#define YYLSP_NEEDED 0



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




/* Copy the first part of user declarations.  */
#line 2 "grammar.y"

#include <storage.h>
#include <node.h>
#include <hash.h>
#include <assoc.h>
#include <setjmp.h>
#define catch_err(c) {longjmp_on_err = 1; if(!setjmp(longjmp_buf))c; longjmp_on_err = 0;}

extern int longjmp_on_err;
extern jmp_buf longjmp_buf;

node_ptr parse_tree;


/* Enabling traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 0
#endif

/* Enabling the token table.  */
#ifndef YYTOKEN_TABLE
# define YYTOKEN_TABLE 0
#endif

#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE
#line 16 "grammar.y"
{
  node_ptr node;
}
/* Line 193 of yacc.c.  */
#line 328 "y.tab.c"
	YYSTYPE;
# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
# define YYSTYPE_IS_TRIVIAL 1
#endif



/* Copy the second part of user declarations.  */


/* Line 216 of yacc.c.  */
#line 341 "y.tab.c"

#ifdef short
# undef short
#endif

#ifdef YYTYPE_UINT8
typedef YYTYPE_UINT8 yytype_uint8;
#else
typedef unsigned char yytype_uint8;
#endif

#ifdef YYTYPE_INT8
typedef YYTYPE_INT8 yytype_int8;
#elif (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
typedef signed char yytype_int8;
#else
typedef short int yytype_int8;
#endif

#ifdef YYTYPE_UINT16
typedef YYTYPE_UINT16 yytype_uint16;
#else
typedef unsigned short int yytype_uint16;
#endif

#ifdef YYTYPE_INT16
typedef YYTYPE_INT16 yytype_int16;
#else
typedef short int yytype_int16;
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif ! defined YYSIZE_T && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned int
# endif
#endif

#define YYSIZE_MAXIMUM ((YYSIZE_T) -1)

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(msgid) dgettext ("bison-runtime", msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(msgid) msgid
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(e) ((void) (e))
#else
# define YYUSE(e) /* empty */
#endif

/* Identity function, used to suppress warnings about constant conditions.  */
#ifndef lint
# define YYID(n) (n)
#else
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static int
YYID (int i)
#else
static int
YYID (i)
    int i;
#endif
{
  return i;
}
#endif

#if ! defined yyoverflow || YYERROR_VERBOSE

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined _STDLIB_H && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#     ifndef _STDLIB_H
#      define _STDLIB_H 1
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's `empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (YYID (0))
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined _STDLIB_H \
       && ! ((defined YYMALLOC || defined malloc) \
	     && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef _STDLIB_H
#    define _STDLIB_H 1
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined _STDLIB_H && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined _STDLIB_H && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* ! defined yyoverflow || YYERROR_VERBOSE */


#if (! defined yyoverflow \
     && (! defined __cplusplus \
	 || (defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yytype_int16 yyss;
  YYSTYPE yyvs;
  };

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (yytype_int16) + sizeof (YYSTYPE)) \
      + YYSTACK_GAP_MAXIMUM)

/* Copy COUNT objects from FROM to TO.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(To, From, Count) \
      __builtin_memcpy (To, From, (Count) * sizeof (*(From)))
#  else
#   define YYCOPY(To, From, Count)		\
      do					\
	{					\
	  YYSIZE_T yyi;				\
	  for (yyi = 0; yyi < (Count); yyi++)	\
	    (To)[yyi] = (From)[yyi];		\
	}					\
      while (YYID (0))
#  endif
# endif

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack)					\
    do									\
      {									\
	YYSIZE_T yynewbytes;						\
	YYCOPY (&yyptr->Stack, Stack, yysize);				\
	Stack = &yyptr->Stack;						\
	yynewbytes = yystacksize * sizeof (*Stack) + YYSTACK_GAP_MAXIMUM; \
	yyptr += yynewbytes / sizeof (*yyptr);				\
      }									\
    while (YYID (0))

#endif

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  61
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   1184

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  108
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  43
/* YYNRULES -- Number of rules.  */
#define YYNRULES  142
/* YYNRULES -- Number of states.  */
#define YYNSTATES  301

/* YYTRANSLATE(YYLEX) -- Bison symbol number corresponding to YYLEX.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   362

#define YYTRANSLATE(YYX)						\
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[YYLEX] -- Bison symbol number corresponding to YYLEX.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
      55,    56,    57,    58,    59,    60,    61,    62,    63,    64,
      65,    66,    67,    68,    69,    70,    71,    72,    73,    74,
      75,    76,    77,    78,    79,    80,    81,    82,    83,    84,
      85,    86,    87,    88,    89,    90,    91,    92,    93,    94,
      95,    96,    97,    98,    99,   100,   101,   102,   103,   104,
     105,   106,   107
};

#if YYDEBUG
/* YYPRHS[YYN] -- Index of the first RHS symbol of rule number YYN in
   YYRHS.  */
static const yytype_uint16 yyprhs[] =
{
       0,     0,     3,     5,     7,     9,    12,    16,    18,    23,
      24,    27,    29,    31,    33,    35,    37,    39,    41,    43,
      45,    47,    49,    51,    53,    56,    59,    62,    66,    67,
      73,    75,    79,    81,    86,    89,    91,    93,    98,   102,
     105,   108,   111,   114,   117,   118,   124,   127,   128,   134,
     136,   141,   146,   149,   152,   155,   158,   160,   164,   166,
     170,   172,   176,   178,   182,   184,   186,   190,   195,   197,
     200,   203,   208,   213,   215,   217,   219,   221,   223,   225,
     229,   233,   237,   241,   245,   248,   251,   254,   257,   260,
     263,   266,   273,   280,   288,   296,   300,   304,   308,   312,
     316,   321,   325,   329,   333,   337,   341,   345,   349,   353,
     357,   361,   365,   369,   373,   377,   381,   389,   396,   403,
     405,   409,   411,   413,   415,   417,   418,   424,   426,   429,
     433,   437,   441,   447,   450,   454,   458,   462,   466,   469,
     472,   474,   478
};

/* YYRHS -- A `-1'-separated list of the rules' RHS.  */
static const yytype_int16 yyrhs[] =
{
     109,     0,    -1,   110,    -1,   147,    -1,   111,    -1,   110,
     111,    -1,    18,   112,   113,    -1,    63,    -1,    63,    50,
     136,    49,    -1,    -1,   113,   114,    -1,   116,    -1,   123,
      -1,   124,    -1,   125,    -1,   126,    -1,   127,    -1,   132,
      -1,   133,    -1,   134,    -1,   129,    -1,   117,    -1,   118,
      -1,   115,    -1,    35,    63,    -1,    32,   119,    -1,    37,
     119,    -1,    36,   138,    51,    -1,    -1,   119,   139,    60,
     120,    51,    -1,    44,    -1,    46,   135,    45,    -1,   121,
      -1,    43,   122,    42,   120,    -1,    17,   121,    -1,   122,
      -1,    63,    -1,    63,    50,   137,    49,    -1,   140,    53,
     140,    -1,    22,    63,    -1,    30,   142,    -1,    29,   142,
      -1,    28,   142,    -1,    31,   128,    -1,    -1,   128,   139,
      54,   142,    51,    -1,    20,   130,    -1,    -1,   130,   131,
      54,   142,    51,    -1,   139,    -1,   106,    50,   139,    49,
      -1,   105,    50,   139,    49,    -1,    26,   141,    -1,    25,
     142,    -1,    24,   143,    -1,    23,   142,    -1,   145,    -1,
     135,    66,   145,    -1,    63,    -1,   136,    66,    63,    -1,
     142,    -1,   137,    66,   142,    -1,   139,    -1,   138,    66,
     139,    -1,    63,    -1,    58,    -1,   139,   107,    63,    -1,
     139,    48,   142,    47,    -1,    64,    -1,   101,    64,    -1,
     100,    64,    -1,    34,   138,    60,   142,    -1,    33,   138,
      60,   142,    -1,   142,    -1,   139,    -1,   140,    -1,   122,
      -1,    56,    -1,    55,    -1,    50,   142,    49,    -1,   142,
      67,   142,    -1,   142,    68,   142,    -1,   142,    69,   142,
      -1,   142,    70,   142,    -1,    71,   142,    -1,    87,   142,
      -1,    86,   142,    -1,    85,   142,    -1,    84,   142,    -1,
      83,   142,    -1,    82,   142,    -1,    80,    48,   142,    79,
     142,    47,    -1,    81,    48,   142,    79,   142,    47,    -1,
      80,    48,   142,    74,   122,   142,    47,    -1,    81,    48,
     142,    74,   122,   142,    47,    -1,    78,   122,   142,    -1,
      76,   122,   142,    -1,    77,   122,   142,    -1,    75,   122,
     142,    -1,    62,   146,    61,    -1,   106,    50,   139,    49,
      -1,   142,   101,   142,    -1,   142,   100,   142,    -1,   142,
     103,   142,    -1,   142,   102,   142,    -1,   142,    99,   142,
      -1,   142,    95,   142,    -1,   142,    94,   142,    -1,   142,
      93,   142,    -1,   142,    92,   142,    -1,   142,    91,   142,
      -1,   142,    90,   142,    -1,    46,   144,    45,    -1,   142,
      96,   142,    -1,   142,    98,   142,    -1,   142,    97,   142,
      -1,    57,    48,    63,    95,   122,    47,   142,    -1,    73,
      48,   142,    66,   142,    47,    -1,    72,    48,   142,    66,
     142,    47,    -1,   145,    -1,   144,    66,   145,    -1,    63,
      -1,   140,    -1,    56,    -1,    55,    -1,    -1,   142,    60,
     142,    51,   146,    -1,   148,    -1,   147,   148,    -1,    25,
     142,    51,    -1,    24,   142,    51,    -1,     7,   150,    51,
      -1,     6,   139,    54,   142,    51,    -1,     5,    51,    -1,
       4,   142,    51,    -1,    30,   142,    51,    -1,    23,   142,
      51,    -1,    29,   142,    51,    -1,     3,    51,    -1,     1,
      51,    -1,    64,    -1,   150,   107,    64,    -1,   149,   107,
      64,    -1
};

/* YYRLINE[YYN] -- source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,    72,    72,    73,    76,    77,    81,    84,    85,    88,
      89,    92,    93,    94,    95,    96,    97,    98,    99,   100,
     101,   102,   103,   104,   107,   110,   113,   116,   119,   120,
     124,   125,   126,   127,   128,   129,   132,   133,   136,   139,
     142,   145,   148,   151,   154,   155,   159,   162,   163,   167,
     168,   169,   172,   173,   176,   179,   183,   184,   187,   188,
     191,   192,   195,   196,   199,   200,   201,   202,   205,   206,
     208,   211,   212,   213,   215,   216,   217,   218,   219,   220,
     221,   222,   223,   224,   225,   226,   227,   228,   229,   230,
     231,   232,   233,   234,   236,   238,   239,   240,   241,   242,
     243,   244,   245,   246,   247,   248,   249,   250,   251,   252,
     253,   254,   255,   256,   257,   258,   260,   264,   265,   268,
     269,   272,   273,   274,   275,   278,   279,   285,   286,   289,
     290,   291,   292,   293,   294,   295,   296,   297,   298,   299,
     302,   303,   306
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || YYTOKEN_TABLE
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "RESET", "EVAL", "STEP", "LET", "GOTO",
  "MAXU", "MINU", "ABU", "EBU", "AU", "EU", "CONTEXT", "LAMBDA", "MODTYPE",
  "PROCESS", "MODULE", "ASYNC", "ASSIGN", "CONSTANT", "ISA", "FAIRNESS",
  "COMPUTE", "SPEC", "PRINT", "FORMAT", "INVAR", "TRANS", "INIT", "DEFINE",
  "VAR", "EXPOSE", "HIDE", "IMPLEMENTS", "OUTPUT", "INPUT", "BDD", "OVER",
  "LIST", "SCALAR", "OF", "ARRAY", "BOOLEAN", "RCB", "LCB", "RB", "LB",
  "RP", "LP", "SEMI", "ATLINE", "TWODOTS", "EQDEF", "TRUEEXP", "FALSEEXP",
  "SIGMA", "SELF", "APROPOS", "COLON", "ESAC", "CASE", "ATOM", "NUMBER",
  "QUOTE", "COMMA", "IMPLIES", "IFF", "OR", "AND", "NOT", "MAX", "MIN",
  "BUNTIL", "ABG", "ABF", "EBG", "EBF", "UNTIL", "A", "E", "AG", "EG",
  "AF", "EF", "AX", "EX", "EPATH", "APATH", "GE", "LE", "GT", "LT",
  "NOTEQUAL", "EQUAL", "UNION", "SETNOTIN", "SETIN", "MOD", "MINUS",
  "PLUS", "DIVIDE", "TIMES", "UMINUS", "SMALLINIT", "NEXT", "DOT",
  "$accept", "begin", "modules", "module", "moduletype", "declarations",
  "declaration", "implements", "var", "input", "output", "vlist", "type",
  "usertype", "subrange", "isa", "init", "trans", "invar", "define",
  "dlist", "assign", "alist", "alhs", "spec", "compute", "fairness",
  "neconstlist", "neatomlist", "neexprlist", "netermlist", "term",
  "number", "hexpr", "expr", "cexpr", "neatomset", "constant", "caselist",
  "commandlist", "command", "trace", "state", 0
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[YYLEX-NUM] -- Internal token number corresponding to
   token YYLEX-NUM.  */
static const yytype_uint16 yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284,
     285,   286,   287,   288,   289,   290,   291,   292,   293,   294,
     295,   296,   297,   298,   299,   300,   301,   302,   303,   304,
     305,   306,   307,   308,   309,   310,   311,   312,   313,   314,
     315,   316,   317,   318,   319,   320,   321,   322,   323,   324,
     325,   326,   327,   328,   329,   330,   331,   332,   333,   334,
     335,   336,   337,   338,   339,   340,   341,   342,   343,   344,
     345,   346,   347,   348,   349,   350,   351,   352,   353,   354,
     355,   356,   357,   358,   359,   360,   361,   362
};
# endif

/* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,   108,   109,   109,   110,   110,   111,   112,   112,   113,
     113,   114,   114,   114,   114,   114,   114,   114,   114,   114,
     114,   114,   114,   114,   115,   116,   117,   118,   119,   119,
     120,   120,   120,   120,   120,   120,   121,   121,   122,   123,
     124,   125,   126,   127,   128,   128,   129,   130,   130,   131,
     131,   131,   132,   132,   133,   134,   135,   135,   136,   136,
     137,   137,   138,   138,   139,   139,   139,   139,   140,   140,
     140,   141,   141,   141,   142,   142,   142,   142,   142,   142,
     142,   142,   142,   142,   142,   142,   142,   142,   142,   142,
     142,   142,   142,   142,   142,   142,   142,   142,   142,   142,
     142,   142,   142,   142,   142,   142,   142,   142,   142,   142,
     142,   142,   142,   142,   142,   142,   142,   143,   143,   144,
     144,   145,   145,   145,   145,   146,   146,   147,   147,   148,
     148,   148,   148,   148,   148,   148,   148,   148,   148,   148,
     149,   149,   150
};

/* YYR2[YYN] -- Number of symbols composing right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     1,     1,     1,     2,     3,     1,     4,     0,
       2,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     2,     2,     2,     3,     0,     5,
       1,     3,     1,     4,     2,     1,     1,     4,     3,     2,
       2,     2,     2,     2,     0,     5,     2,     0,     5,     1,
       4,     4,     2,     2,     2,     2,     1,     3,     1,     3,
       1,     3,     1,     3,     1,     1,     3,     4,     1,     2,
       2,     4,     4,     1,     1,     1,     1,     1,     1,     3,
       3,     3,     3,     3,     2,     2,     2,     2,     2,     2,
       2,     6,     6,     7,     7,     3,     3,     3,     3,     3,
       4,     3,     3,     3,     3,     3,     3,     3,     3,     3,
       3,     3,     3,     3,     3,     3,     7,     6,     6,     1,
       3,     1,     1,     1,     1,     0,     5,     1,     2,     3,
       3,     3,     5,     2,     3,     3,     3,     3,     2,     2,
       1,     3,     3
};

/* YYDEFACT[STATE-NAME] -- Default rule to reduce with in state
   STATE-NUM when YYTABLE doesn't specify something else to do.  Zero
   means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     2,     4,     0,   127,   139,   138,
       0,     0,    78,    77,     0,    65,   125,    64,    68,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,    76,    74,    75,     0,   133,
       0,   140,     0,     0,     7,     9,     0,     0,     0,     0,
       0,     1,     5,   128,   124,   123,   121,   122,     0,   119,
       0,     0,     0,     0,    84,     0,     0,     0,     0,     0,
       0,     0,    90,    89,    88,    87,    86,    85,    70,    69,
       0,     0,     0,     0,   134,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   131,     0,     0,     6,   136,
     130,   129,   137,   135,   112,     0,    79,     0,     0,    99,
      98,    96,    97,    95,     0,     0,     0,     0,    66,    38,
      80,    81,    82,    83,   111,   110,   109,   108,   107,   106,
     113,   115,   114,   105,   102,   101,   104,   103,     0,   142,
     141,    58,     0,    47,     0,     0,     0,     0,     0,     0,
       0,     0,    44,    28,     0,     0,    28,    10,    23,    11,
      21,    22,    12,    13,    14,    15,    16,    20,    17,    18,
      19,   120,     0,     0,     0,     0,     0,     0,   100,    67,
     132,     8,     0,    46,    39,    55,     0,     0,    54,    53,
       0,     0,    52,    73,    42,    41,    40,    43,    25,    24,
       0,    62,    26,     0,   125,     0,     0,     0,     0,    59,
       0,     0,     0,    49,     0,     0,     0,     0,     0,     0,
      27,     0,     0,   126,     0,    91,     0,    92,     0,     0,
       0,     0,     0,     0,     0,     0,     0,    63,   116,    93,
      94,     0,     0,     0,     0,     0,    72,    71,     0,     0,
       0,    30,     0,    36,     0,    32,    35,    51,    50,    48,
       0,     0,    45,    34,     0,     0,    56,     0,    29,   118,
     117,     0,    31,     0,     0,    60,    33,    57,    37,     0,
      61
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,    13,    14,    15,    55,   118,   177,   178,   179,   180,
     181,   218,   274,   275,    45,   182,   183,   184,   185,   186,
     217,   187,   203,   232,   188,   189,   190,   285,   162,   294,
     220,    46,    47,   212,    72,   208,    68,    69,    73,    16,
      17,    52,    53
};

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
#define YYPACT_NINF -125
static const yytype_int16 yypact[] =
{
     263,   -38,   -35,   291,    -5,    22,     1,     5,   291,   291,
     291,   291,   291,    59,    61,  -125,   150,  -125,  -125,  -125,
      71,   291,  -125,  -125,    63,  -125,   291,  -125,  -125,   291,
     -17,   -17,   -17,   -17,    65,    74,   291,   291,   291,   291,
     291,   291,    69,    83,    99,  -125,   -25,   110,   608,  -125,
     -44,  -125,    45,   -26,   120,  -125,   645,   682,   719,   756,
     793,  -125,  -125,  -125,  -125,  -125,  -125,  -125,   -13,  -125,
     571,   113,   515,   121,   626,   291,   110,   291,   291,   291,
     291,   291,   626,   626,   626,   626,   626,   626,  -125,  -125,
      22,   291,   123,   -17,  -125,   291,   291,   291,   291,   291,
     291,   291,   291,   291,   291,   291,   291,   291,   291,   291,
     291,   291,   291,   291,   124,  -125,   125,   127,   400,  -125,
    -125,  -125,  -125,  -125,  -125,    71,  -125,    89,   291,  -125,
     626,   626,   626,   626,  1030,  1067,   -46,   312,  -125,  -125,
    1081,   552,   590,   626,    40,    40,    40,    40,    40,    40,
      18,    29,    29,    58,   -47,   -47,  -125,  -125,   830,  -125,
    -125,  -125,   -22,  -125,   128,   291,    73,   291,   244,   291,
     291,   291,  -125,  -125,   130,    22,  -125,  -125,  -125,  -125,
    -125,  -125,  -125,  -125,  -125,  -125,  -125,  -125,  -125,  -125,
    -125,  -125,   -17,   867,   -17,   291,   -17,   291,  -125,  -125,
    -125,  -125,   132,   -15,  -125,  1081,   139,   148,  -125,  1081,
      22,    22,  -125,  1081,  1081,  1081,  1081,    22,    22,  -125,
      -9,   -25,    22,   151,   291,   291,   349,   291,   386,  -125,
     147,   152,   146,   -25,   291,   291,    -6,    -2,   -37,   -36,
    -125,    22,   291,  -125,   423,  -125,   460,  -125,    22,    22,
     291,   955,   993,   291,   291,   291,    23,   -25,  1081,  -125,
    -125,   -34,   -18,   904,   291,   291,  1081,  1081,   941,   138,
     -17,  -125,    71,   153,   154,  -125,  -125,  -125,  -125,  -125,
     497,   534,  -125,  -125,   162,    -4,  -125,   291,  -125,  -125,
    -125,    23,  -125,    71,   -21,  1081,  -125,  -125,  -125,   291,
    1081
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -125,  -125,  -125,   192,  -125,  -125,  -125,  -125,  -125,  -125,
    -125,    31,   -83,   -60,   -11,  -125,  -125,  -125,  -125,  -125,
    -125,  -125,  -125,  -125,  -125,  -125,  -125,  -125,  -125,  -125,
     -33,    24,    19,  -125,    -3,  -125,  -125,  -124,   -14,  -125,
     196,  -125,  -125
};

/* YYTABLE[YYPACT[STATE-NUM]].  What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule which
   number is the opposite.  If zero, do what YYDEFACT says.
   If YYTABLE_NINF, syntax error.  */
#define YYTABLE_NINF -4
static const yytype_int16 yytable[] =
{
      48,   191,    91,   198,    91,    56,    57,    58,    59,    60,
     113,    91,    91,    18,    91,   277,    19,   255,    70,    75,
      77,    78,    79,    91,   256,   115,    74,   201,   298,    50,
      91,   278,   124,    82,    83,    84,    85,    86,    87,    67,
     269,   292,   240,    25,   202,   299,    49,    28,    27,    76,
      76,    76,    76,   125,   253,   111,   112,   241,   254,    61,
     241,    92,   293,    92,   241,    51,   270,   271,    54,   272,
      92,    92,   130,    92,   131,   132,   133,   134,   135,     7,
      25,   116,    92,    42,    43,    27,   273,    28,   137,    92,
     230,   231,   140,   141,   142,   143,   144,   145,   146,   147,
     148,   149,   150,   151,   152,   153,   154,   155,   156,   157,
     158,    71,   139,    80,   136,   106,   107,   108,   109,   110,
     111,   112,    81,    42,    43,   193,    64,    65,   108,   109,
     110,   111,   112,    88,    66,    28,   105,   106,   107,   108,
     109,   110,   111,   112,    67,   206,   207,    89,   286,    90,
      -3,     1,   114,     2,     3,     4,     5,     6,   109,   110,
     111,   112,   205,    93,   209,   213,   214,   215,   216,   297,
     117,    42,    43,     8,     9,    10,   127,   236,   237,    11,
      12,   223,   129,   225,   192,   227,   138,   234,   159,   160,
     161,   204,   226,   219,   228,   229,   235,   248,   242,   221,
     250,   273,   249,   287,   291,   288,    62,   222,   296,   283,
     243,    76,    63,    76,     0,    76,     0,     0,     0,     0,
       0,     0,   244,     0,   246,     0,     0,   233,     0,     0,
       0,   251,   252,     0,   221,   221,     0,     0,     0,   258,
       0,   238,   239,     0,     0,   276,   239,   263,     0,     0,
     266,   267,   268,     0,     0,     0,     0,     0,     0,   284,
       0,   280,   281,     0,     1,   257,     2,     3,     4,     5,
       6,     0,   261,   262,     0,    76,     0,   210,   211,     0,
     276,     7,     0,     0,   295,     0,     8,     9,    10,    76,
      20,    67,    11,    12,    21,     0,   300,     0,     0,    22,
      23,    24,    25,     0,     0,     0,    26,    27,    28,     0,
      76,     0,    67,     0,     0,    29,     0,     0,     0,    30,
      31,    32,    33,     0,    34,    35,    36,    37,    38,    39,
      40,    41,     0,     0,     0,     0,     0,    20,     0,     0,
       0,    21,     0,     0,    42,    43,    22,    23,    24,    25,
      44,     0,     0,    26,    27,    28,     0,     0,     0,   199,
       0,     0,    29,     0,     0,     0,    30,    31,    32,    33,
       0,    34,    35,    36,    37,    38,    39,    40,    41,    95,
      96,    97,    98,     0,     0,     0,     0,     0,     0,     0,
       0,    42,    43,     0,     0,     0,   245,    44,     0,     0,
       0,     0,    99,   100,   101,   102,   103,   104,   105,   106,
     107,   108,   109,   110,   111,   112,    95,    96,    97,    98,
     163,     0,   164,   165,   166,   167,   168,     0,   169,   170,
     171,   172,   173,   247,     0,   174,   175,   176,     0,    99,
     100,   101,   102,   103,   104,   105,   106,   107,   108,   109,
     110,   111,   112,    95,    96,    97,    98,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     259,     0,     0,     0,     0,     0,    99,   100,   101,   102,
     103,   104,   105,   106,   107,   108,   109,   110,   111,   112,
      95,    96,    97,    98,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   260,     0,     0,
       0,     0,     0,    99,   100,   101,   102,   103,   104,   105,
     106,   107,   108,   109,   110,   111,   112,    95,    96,    97,
      98,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   289,     0,     0,     0,     0,     0,
      99,   100,   101,   102,   103,   104,   105,   106,   107,   108,
     109,   110,   111,   112,    95,    96,    97,    98,     0,     0,
       0,     0,     0,     0,     0,   128,     0,     0,     0,     0,
       0,   290,    95,    96,    97,    98,     0,    99,   100,   101,
     102,   103,   104,   105,   106,   107,   108,   109,   110,   111,
     112,    95,    96,    97,    98,    99,   100,   101,   102,   103,
     104,   105,   106,   107,   108,   109,   110,   111,   112,     0,
     126,    97,    98,     0,    99,   100,   101,   102,   103,   104,
     105,   106,   107,   108,   109,   110,   111,   112,    95,    96,
      97,    98,    99,   100,   101,   102,   103,   104,   105,   106,
     107,   108,   109,   110,   111,   112,     0,     0,     0,    94,
      98,    99,   100,   101,   102,   103,   104,   105,   106,   107,
     108,   109,   110,   111,   112,    95,    96,    97,    98,     0,
      99,   100,   101,   102,   103,   104,   105,   106,   107,   108,
     109,   110,   111,   112,     0,     0,   119,     0,    99,   100,
     101,   102,   103,   104,   105,   106,   107,   108,   109,   110,
     111,   112,    95,    96,    97,    98,    99,   100,   101,   102,
     103,   104,   105,   106,   107,   108,   109,   110,   111,   112,
       0,     0,     0,   120,     0,    99,   100,   101,   102,   103,
     104,   105,   106,   107,   108,   109,   110,   111,   112,    95,
      96,    97,    98,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     121,     0,    99,   100,   101,   102,   103,   104,   105,   106,
     107,   108,   109,   110,   111,   112,    95,    96,    97,    98,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   122,     0,    99,
     100,   101,   102,   103,   104,   105,   106,   107,   108,   109,
     110,   111,   112,    95,    96,    97,    98,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   123,     0,    99,   100,   101,   102,
     103,   104,   105,   106,   107,   108,   109,   110,   111,   112,
      95,    96,    97,    98,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   200,     0,    99,   100,   101,   102,   103,   104,   105,
     106,   107,   108,   109,   110,   111,   112,    95,    96,    97,
      98,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   224,     0,
      99,   100,   101,   102,   103,   104,   105,   106,   107,   108,
     109,   110,   111,   112,    95,    96,    97,    98,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   279,     0,    99,   100,   101,
     102,   103,   104,   105,   106,   107,   108,   109,   110,   111,
     112,    95,    96,    97,    98,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   282,     0,    99,   100,   101,   102,   103,   104,
     105,   106,   107,   108,   109,   110,   111,   112,    95,    96,
      97,    98,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   264,    95,    96,    97,    98,     0,     0,     0,     0,
       0,    99,   100,   101,   102,   103,   104,   105,   106,   107,
     108,   109,   110,   111,   112,    99,   100,   101,   102,   103,
     104,   105,   106,   107,   108,   109,   110,   111,   112,   265,
      95,    96,    97,    98,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,    99,   100,   101,   102,   103,   104,   105,
     106,   107,   108,   109,   110,   111,   112,    95,    96,    97,
      98,     0,     0,     0,   194,     0,     0,     0,     0,   195,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
      99,   100,   101,   102,   103,   104,   105,   106,   107,   108,
     109,   110,   111,   112,    95,    96,    97,    98,     0,     0,
       0,   196,     0,     0,     0,     0,   197,     0,    95,    96,
      97,    98,     0,     0,     0,     0,     0,    99,   100,   101,
     102,   103,   104,   105,   106,   107,   108,   109,   110,   111,
     112,    99,   100,   101,   102,   103,   104,   105,   106,   107,
     108,   109,   110,   111,   112
};

static const yytype_int16 yycheck[] =
{
       3,   125,    48,    49,    48,     8,     9,    10,    11,    12,
      54,    48,    48,    51,    48,    49,    51,    54,    21,    30,
      31,    32,    33,    48,    60,    51,    29,    49,    49,     5,
      48,    49,    45,    36,    37,    38,    39,    40,    41,    20,
      17,    45,    51,    58,    66,    66,    51,    64,    63,    30,
      31,    32,    33,    66,    60,   102,   103,    66,    60,     0,
      66,   107,    66,   107,    66,    64,    43,    44,    63,    46,
     107,   107,    75,   107,    77,    78,    79,    80,    81,    18,
      58,   107,   107,   100,   101,    63,    63,    64,    91,   107,
     105,   106,    95,    96,    97,    98,    99,   100,   101,   102,
     103,   104,   105,   106,   107,   108,   109,   110,   111,   112,
     113,    48,    93,    48,    90,    97,    98,    99,   100,   101,
     102,   103,    48,   100,   101,   128,    55,    56,    99,   100,
     101,   102,   103,    64,    63,    64,    96,    97,    98,    99,
     100,   101,   102,   103,   125,    72,    73,    64,   272,    50,
       0,     1,   107,     3,     4,     5,     6,     7,   100,   101,
     102,   103,   165,    53,   167,   168,   169,   170,   171,   293,
      50,   100,   101,    23,    24,    25,    63,   210,   211,    29,
      30,   192,    61,   194,    95,   196,    63,    48,    64,    64,
      63,    63,   195,    63,   197,    63,    48,    50,    47,   175,
      54,    63,    50,    50,    42,    51,    14,   176,   291,   269,
     224,   192,    16,   194,    -1,   196,    -1,    -1,    -1,    -1,
      -1,    -1,   225,    -1,   227,    -1,    -1,   203,    -1,    -1,
      -1,   234,   235,    -1,   210,   211,    -1,    -1,    -1,   242,
      -1,   217,   218,    -1,    -1,   256,   222,   250,    -1,    -1,
     253,   254,   255,    -1,    -1,    -1,    -1,    -1,    -1,   270,
      -1,   264,   265,    -1,     1,   241,     3,     4,     5,     6,
       7,    -1,   248,   249,    -1,   256,    -1,    33,    34,    -1,
     291,    18,    -1,    -1,   287,    -1,    23,    24,    25,   270,
      46,   272,    29,    30,    50,    -1,   299,    -1,    -1,    55,
      56,    57,    58,    -1,    -1,    -1,    62,    63,    64,    -1,
     291,    -1,   293,    -1,    -1,    71,    -1,    -1,    -1,    75,
      76,    77,    78,    -1,    80,    81,    82,    83,    84,    85,
      86,    87,    -1,    -1,    -1,    -1,    -1,    46,    -1,    -1,
      -1,    50,    -1,    -1,   100,   101,    55,    56,    57,    58,
     106,    -1,    -1,    62,    63,    64,    -1,    -1,    -1,    47,
      -1,    -1,    71,    -1,    -1,    -1,    75,    76,    77,    78,
      -1,    80,    81,    82,    83,    84,    85,    86,    87,    67,
      68,    69,    70,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   100,   101,    -1,    -1,    -1,    47,   106,    -1,    -1,
      -1,    -1,    90,    91,    92,    93,    94,    95,    96,    97,
      98,    99,   100,   101,   102,   103,    67,    68,    69,    70,
      20,    -1,    22,    23,    24,    25,    26,    -1,    28,    29,
      30,    31,    32,    47,    -1,    35,    36,    37,    -1,    90,
      91,    92,    93,    94,    95,    96,    97,    98,    99,   100,
     101,   102,   103,    67,    68,    69,    70,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      47,    -1,    -1,    -1,    -1,    -1,    90,    91,    92,    93,
      94,    95,    96,    97,    98,    99,   100,   101,   102,   103,
      67,    68,    69,    70,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    47,    -1,    -1,
      -1,    -1,    -1,    90,    91,    92,    93,    94,    95,    96,
      97,    98,    99,   100,   101,   102,   103,    67,    68,    69,
      70,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    47,    -1,    -1,    -1,    -1,    -1,
      90,    91,    92,    93,    94,    95,    96,    97,    98,    99,
     100,   101,   102,   103,    67,    68,    69,    70,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    60,    -1,    -1,    -1,    -1,
      -1,    47,    67,    68,    69,    70,    -1,    90,    91,    92,
      93,    94,    95,    96,    97,    98,    99,   100,   101,   102,
     103,    67,    68,    69,    70,    90,    91,    92,    93,    94,
      95,    96,    97,    98,    99,   100,   101,   102,   103,    -1,
      49,    69,    70,    -1,    90,    91,    92,    93,    94,    95,
      96,    97,    98,    99,   100,   101,   102,   103,    67,    68,
      69,    70,    90,    91,    92,    93,    94,    95,    96,    97,
      98,    99,   100,   101,   102,   103,    -1,    -1,    -1,    51,
      70,    90,    91,    92,    93,    94,    95,    96,    97,    98,
      99,   100,   101,   102,   103,    67,    68,    69,    70,    -1,
      90,    91,    92,    93,    94,    95,    96,    97,    98,    99,
     100,   101,   102,   103,    -1,    -1,    51,    -1,    90,    91,
      92,    93,    94,    95,    96,    97,    98,    99,   100,   101,
     102,   103,    67,    68,    69,    70,    90,    91,    92,    93,
      94,    95,    96,    97,    98,    99,   100,   101,   102,   103,
      -1,    -1,    -1,    51,    -1,    90,    91,    92,    93,    94,
      95,    96,    97,    98,    99,   100,   101,   102,   103,    67,
      68,    69,    70,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      51,    -1,    90,    91,    92,    93,    94,    95,    96,    97,
      98,    99,   100,   101,   102,   103,    67,    68,    69,    70,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    51,    -1,    90,
      91,    92,    93,    94,    95,    96,    97,    98,    99,   100,
     101,   102,   103,    67,    68,    69,    70,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    51,    -1,    90,    91,    92,    93,
      94,    95,    96,    97,    98,    99,   100,   101,   102,   103,
      67,    68,    69,    70,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    51,    -1,    90,    91,    92,    93,    94,    95,    96,
      97,    98,    99,   100,   101,   102,   103,    67,    68,    69,
      70,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    51,    -1,
      90,    91,    92,    93,    94,    95,    96,    97,    98,    99,
     100,   101,   102,   103,    67,    68,    69,    70,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    51,    -1,    90,    91,    92,
      93,    94,    95,    96,    97,    98,    99,   100,   101,   102,
     103,    67,    68,    69,    70,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    51,    -1,    90,    91,    92,    93,    94,    95,
      96,    97,    98,    99,   100,   101,   102,   103,    67,    68,
      69,    70,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    66,    67,    68,    69,    70,    -1,    -1,    -1,    -1,
      -1,    90,    91,    92,    93,    94,    95,    96,    97,    98,
      99,   100,   101,   102,   103,    90,    91,    92,    93,    94,
      95,    96,    97,    98,    99,   100,   101,   102,   103,    66,
      67,    68,    69,    70,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    90,    91,    92,    93,    94,    95,    96,
      97,    98,    99,   100,   101,   102,   103,    67,    68,    69,
      70,    -1,    -1,    -1,    74,    -1,    -1,    -1,    -1,    79,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      90,    91,    92,    93,    94,    95,    96,    97,    98,    99,
     100,   101,   102,   103,    67,    68,    69,    70,    -1,    -1,
      -1,    74,    -1,    -1,    -1,    -1,    79,    -1,    67,    68,
      69,    70,    -1,    -1,    -1,    -1,    -1,    90,    91,    92,
      93,    94,    95,    96,    97,    98,    99,   100,   101,   102,
     103,    90,    91,    92,    93,    94,    95,    96,    97,    98,
      99,   100,   101,   102,   103
};

/* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
   symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,     1,     3,     4,     5,     6,     7,    18,    23,    24,
      25,    29,    30,   109,   110,   111,   147,   148,    51,    51,
      46,    50,    55,    56,    57,    58,    62,    63,    64,    71,
      75,    76,    77,    78,    80,    81,    82,    83,    84,    85,
      86,    87,   100,   101,   106,   122,   139,   140,   142,    51,
     139,    64,   149,   150,    63,   112,   142,   142,   142,   142,
     142,     0,   111,   148,    55,    56,    63,   140,   144,   145,
     142,    48,   142,   146,   142,   122,   140,   122,   122,   122,
      48,    48,   142,   142,   142,   142,   142,   142,    64,    64,
      50,    48,   107,    53,    51,    67,    68,    69,    70,    90,
      91,    92,    93,    94,    95,    96,    97,    98,    99,   100,
     101,   102,   103,    54,   107,    51,   107,    50,   113,    51,
      51,    51,    51,    51,    45,    66,    49,    63,    60,    61,
     142,   142,   142,   142,   142,   142,   139,   142,    63,   140,
     142,   142,   142,   142,   142,   142,   142,   142,   142,   142,
     142,   142,   142,   142,   142,   142,   142,   142,   142,    64,
      64,    63,   136,    20,    22,    23,    24,    25,    26,    28,
      29,    30,    31,    32,    35,    36,    37,   114,   115,   116,
     117,   118,   123,   124,   125,   126,   127,   129,   132,   133,
     134,   145,    95,   142,    74,    79,    74,    79,    49,    47,
      51,    49,    66,   130,    63,   142,    72,    73,   143,   142,
      33,    34,   141,   142,   142,   142,   142,   128,   119,    63,
     138,   139,   119,   122,    51,   122,   142,   122,   142,    63,
     105,   106,   131,   139,    48,    48,   138,   138,   139,   139,
      51,    66,    47,   146,   142,    47,   142,    47,    50,    50,
      54,   142,   142,    60,    60,    54,    60,   139,   142,    47,
      47,   139,   139,   142,    66,    66,   142,   142,   142,    17,
      43,    44,    46,    63,   120,   121,   122,    49,    49,    51,
     142,   142,    51,   121,   122,   135,   145,    50,    51,    47,
      47,    42,    45,    66,   137,   142,   120,   145,    49,    66,
     142
};

#define yyerrok		(yyerrstatus = 0)
#define yyclearin	(yychar = YYEMPTY)
#define YYEMPTY		(-2)
#define YYEOF		0

#define YYACCEPT	goto yyacceptlab
#define YYABORT		goto yyabortlab
#define YYERROR		goto yyerrorlab


/* Like YYERROR except do call yyerror.  This remains here temporarily
   to ease the transition to the new meaning of YYERROR, for GCC.
   Once GCC version 2 has supplanted version 1, this can go.  */

#define YYFAIL		goto yyerrlab

#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)					\
do								\
  if (yychar == YYEMPTY && yylen == 1)				\
    {								\
      yychar = (Token);						\
      yylval = (Value);						\
      yytoken = YYTRANSLATE (yychar);				\
      YYPOPSTACK (1);						\
      goto yybackup;						\
    }								\
  else								\
    {								\
      yyerror (YY_("syntax error: cannot back up")); \
      YYERROR;							\
    }								\
while (YYID (0))


#define YYTERROR	1
#define YYERRCODE	256


/* YYLLOC_DEFAULT -- Set CURRENT to span from RHS[1] to RHS[N].
   If N is 0, then set CURRENT to the empty location which ends
   the previous symbol: RHS[0] (always defined).  */

#define YYRHSLOC(Rhs, K) ((Rhs)[K])
#ifndef YYLLOC_DEFAULT
# define YYLLOC_DEFAULT(Current, Rhs, N)				\
    do									\
      if (YYID (N))                                                    \
	{								\
	  (Current).first_line   = YYRHSLOC (Rhs, 1).first_line;	\
	  (Current).first_column = YYRHSLOC (Rhs, 1).first_column;	\
	  (Current).last_line    = YYRHSLOC (Rhs, N).last_line;		\
	  (Current).last_column  = YYRHSLOC (Rhs, N).last_column;	\
	}								\
      else								\
	{								\
	  (Current).first_line   = (Current).last_line   =		\
	    YYRHSLOC (Rhs, 0).last_line;				\
	  (Current).first_column = (Current).last_column =		\
	    YYRHSLOC (Rhs, 0).last_column;				\
	}								\
    while (YYID (0))
#endif


/* YY_LOCATION_PRINT -- Print the location on the stream.
   This macro was not mandated originally: define only if we know
   we won't break user code: when these are the locations we know.  */

#ifndef YY_LOCATION_PRINT
# if defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL
#  define YY_LOCATION_PRINT(File, Loc)			\
     fprintf (File, "%d.%d-%d.%d",			\
	      (Loc).first_line, (Loc).first_column,	\
	      (Loc).last_line,  (Loc).last_column)
# else
#  define YY_LOCATION_PRINT(File, Loc) ((void) 0)
# endif
#endif


/* YYLEX -- calling `yylex' with the right arguments.  */

#ifdef YYLEX_PARAM
# define YYLEX yylex (YYLEX_PARAM)
#else
# define YYLEX yylex ()
#endif

/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)			\
do {						\
  if (yydebug)					\
    YYFPRINTF Args;				\
} while (YYID (0))

# define YY_SYMBOL_PRINT(Title, Type, Value, Location)			  \
do {									  \
  if (yydebug)								  \
    {									  \
      YYFPRINTF (stderr, "%s ", Title);					  \
      yy_symbol_print (stderr,						  \
		  Type, Value); \
      YYFPRINTF (stderr, "\n");						  \
    }									  \
} while (YYID (0))


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

/*ARGSUSED*/
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
#else
static void
yy_symbol_value_print (yyoutput, yytype, yyvaluep)
    FILE *yyoutput;
    int yytype;
    YYSTYPE const * const yyvaluep;
#endif
{
  if (!yyvaluep)
    return;
# ifdef YYPRINT
  if (yytype < YYNTOKENS)
    YYPRINT (yyoutput, yytoknum[yytype], *yyvaluep);
# else
  YYUSE (yyoutput);
# endif
  switch (yytype)
    {
      default:
	break;
    }
}


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
#else
static void
yy_symbol_print (yyoutput, yytype, yyvaluep)
    FILE *yyoutput;
    int yytype;
    YYSTYPE const * const yyvaluep;
#endif
{
  if (yytype < YYNTOKENS)
    YYFPRINTF (yyoutput, "token %s (", yytname[yytype]);
  else
    YYFPRINTF (yyoutput, "nterm %s (", yytname[yytype]);

  yy_symbol_value_print (yyoutput, yytype, yyvaluep);
  YYFPRINTF (yyoutput, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_stack_print (yytype_int16 *bottom, yytype_int16 *top)
#else
static void
yy_stack_print (bottom, top)
    yytype_int16 *bottom;
    yytype_int16 *top;
#endif
{
  YYFPRINTF (stderr, "Stack now");
  for (; bottom <= top; ++bottom)
    YYFPRINTF (stderr, " %d", *bottom);
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)				\
do {								\
  if (yydebug)							\
    yy_stack_print ((Bottom), (Top));				\
} while (YYID (0))


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_reduce_print (YYSTYPE *yyvsp, int yyrule)
#else
static void
yy_reduce_print (yyvsp, yyrule)
    YYSTYPE *yyvsp;
    int yyrule;
#endif
{
  int yynrhs = yyr2[yyrule];
  int yyi;
  unsigned long int yylno = yyrline[yyrule];
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %lu):\n",
	     yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      fprintf (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr, yyrhs[yyprhs[yyrule] + yyi],
		       &(yyvsp[(yyi + 1) - (yynrhs)])
		       		       );
      fprintf (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)		\
do {					\
  if (yydebug)				\
    yy_reduce_print (yyvsp, Rule); \
} while (YYID (0))

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef	YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif



#if YYERROR_VERBOSE

# ifndef yystrlen
#  if defined __GLIBC__ && defined _STRING_H
#   define yystrlen strlen
#  else
/* Return the length of YYSTR.  */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static YYSIZE_T
yystrlen (const char *yystr)
#else
static YYSIZE_T
yystrlen (yystr)
    const char *yystr;
#endif
{
  YYSIZE_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
#  endif
# endif

# ifndef yystpcpy
#  if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static char *
yystpcpy (char *yydest, const char *yysrc)
#else
static char *
yystpcpy (yydest, yysrc)
    char *yydest;
    const char *yysrc;
#endif
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

# ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYSIZE_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYSIZE_T yyn = 0;
      char const *yyp = yystr;

      for (;;)
	switch (*++yyp)
	  {
	  case '\'':
	  case ',':
	    goto do_not_strip_quotes;

	  case '\\':
	    if (*++yyp != '\\')
	      goto do_not_strip_quotes;
	    /* Fall through.  */
	  default:
	    if (yyres)
	      yyres[yyn] = *yyp;
	    yyn++;
	    break;

	  case '"':
	    if (yyres)
	      yyres[yyn] = '\0';
	    return yyn;
	  }
    do_not_strip_quotes: ;
    }

  if (! yyres)
    return yystrlen (yystr);

  return yystpcpy (yyres, yystr) - yyres;
}
# endif

/* Copy into YYRESULT an error message about the unexpected token
   YYCHAR while in state YYSTATE.  Return the number of bytes copied,
   including the terminating null byte.  If YYRESULT is null, do not
   copy anything; just return the number of bytes that would be
   copied.  As a special case, return 0 if an ordinary "syntax error"
   message will do.  Return YYSIZE_MAXIMUM if overflow occurs during
   size calculation.  */
static YYSIZE_T
yysyntax_error (char *yyresult, int yystate, int yychar)
{
  int yyn = yypact[yystate];

  if (! (YYPACT_NINF < yyn && yyn <= YYLAST))
    return 0;
  else
    {
      int yytype = YYTRANSLATE (yychar);
      YYSIZE_T yysize0 = yytnamerr (0, yytname[yytype]);
      YYSIZE_T yysize = yysize0;
      YYSIZE_T yysize1;
      int yysize_overflow = 0;
      enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
      char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
      int yyx;

# if 0
      /* This is so xgettext sees the translatable formats that are
	 constructed on the fly.  */
      YY_("syntax error, unexpected %s");
      YY_("syntax error, unexpected %s, expecting %s");
      YY_("syntax error, unexpected %s, expecting %s or %s");
      YY_("syntax error, unexpected %s, expecting %s or %s or %s");
      YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s");
# endif
      char *yyfmt;
      char const *yyf;
      static char const yyunexpected[] = "syntax error, unexpected %s";
      static char const yyexpecting[] = ", expecting %s";
      static char const yyor[] = " or %s";
      char yyformat[sizeof yyunexpected
		    + sizeof yyexpecting - 1
		    + ((YYERROR_VERBOSE_ARGS_MAXIMUM - 2)
		       * (sizeof yyor - 1))];
      char const *yyprefix = yyexpecting;

      /* Start YYX at -YYN if negative to avoid negative indexes in
	 YYCHECK.  */
      int yyxbegin = yyn < 0 ? -yyn : 0;

      /* Stay within bounds of both yycheck and yytname.  */
      int yychecklim = YYLAST - yyn + 1;
      int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
      int yycount = 1;

      yyarg[0] = yytname[yytype];
      yyfmt = yystpcpy (yyformat, yyunexpected);

      for (yyx = yyxbegin; yyx < yyxend; ++yyx)
	if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR)
	  {
	    if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
	      {
		yycount = 1;
		yysize = yysize0;
		yyformat[sizeof yyunexpected - 1] = '\0';
		break;
	      }
	    yyarg[yycount++] = yytname[yyx];
	    yysize1 = yysize + yytnamerr (0, yytname[yyx]);
	    yysize_overflow |= (yysize1 < yysize);
	    yysize = yysize1;
	    yyfmt = yystpcpy (yyfmt, yyprefix);
	    yyprefix = yyor;
	  }

      yyf = YY_(yyformat);
      yysize1 = yysize + yystrlen (yyf);
      yysize_overflow |= (yysize1 < yysize);
      yysize = yysize1;

      if (yysize_overflow)
	return YYSIZE_MAXIMUM;

      if (yyresult)
	{
	  /* Avoid sprintf, as that infringes on the user's name space.
	     Don't have undefined behavior even if the translation
	     produced a string with the wrong number of "%s"s.  */
	  char *yyp = yyresult;
	  int yyi = 0;
	  while ((*yyp = *yyf) != '\0')
	    {
	      if (*yyp == '%' && yyf[1] == 's' && yyi < yycount)
		{
		  yyp += yytnamerr (yyp, yyarg[yyi++]);
		  yyf += 2;
		}
	      else
		{
		  yyp++;
		  yyf++;
		}
	    }
	}
      return yysize;
    }
}
#endif /* YYERROR_VERBOSE */


/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

/*ARGSUSED*/
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep)
#else
static void
yydestruct (yymsg, yytype, yyvaluep)
    const char *yymsg;
    int yytype;
    YYSTYPE *yyvaluep;
#endif
{
  YYUSE (yyvaluep);

  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  switch (yytype)
    {

      default:
	break;
    }
}


/* Prevent warnings from -Wmissing-prototypes.  */

#ifdef YYPARSE_PARAM
#if defined __STDC__ || defined __cplusplus
int yyparse (void *YYPARSE_PARAM);
#else
int yyparse ();
#endif
#else /* ! YYPARSE_PARAM */
#if defined __STDC__ || defined __cplusplus
int yyparse (void);
#else
int yyparse ();
#endif
#endif /* ! YYPARSE_PARAM */



/* The look-ahead symbol.  */
int yychar;

/* The semantic value of the look-ahead symbol.  */
YYSTYPE yylval;

/* Number of syntax errors so far.  */
int yynerrs;



/*----------.
| yyparse.  |
`----------*/

#ifdef YYPARSE_PARAM
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
int
yyparse (void *YYPARSE_PARAM)
#else
int
yyparse (YYPARSE_PARAM)
    void *YYPARSE_PARAM;
#endif
#else /* ! YYPARSE_PARAM */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
int
yyparse (void)
#else
int
yyparse ()

#endif
#endif
{
  
  int yystate;
  int yyn;
  int yyresult;
  /* Number of tokens to shift before error messages enabled.  */
  int yyerrstatus;
  /* Look-ahead token as an internal (translated) token number.  */
  int yytoken = 0;
#if YYERROR_VERBOSE
  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYSIZE_T yymsg_alloc = sizeof yymsgbuf;
#endif

  /* Three stacks and their tools:
     `yyss': related to states,
     `yyvs': related to semantic values,
     `yyls': related to locations.

     Refer to the stacks thru separate pointers, to allow yyoverflow
     to reallocate them elsewhere.  */

  /* The state stack.  */
  yytype_int16 yyssa[YYINITDEPTH];
  yytype_int16 *yyss = yyssa;
  yytype_int16 *yyssp;

  /* The semantic value stack.  */
  YYSTYPE yyvsa[YYINITDEPTH];
  YYSTYPE *yyvs = yyvsa;
  YYSTYPE *yyvsp;



#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N))

  YYSIZE_T yystacksize = YYINITDEPTH;

  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;


  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
  yychar = YYEMPTY;		/* Cause a token to be read.  */

  /* Initialize stack pointers.
     Waste one element of value and location stack
     so that they stay on the same level as the state stack.
     The wasted elements are never initialized.  */

  yyssp = yyss;
  yyvsp = yyvs;

  goto yysetstate;

/*------------------------------------------------------------.
| yynewstate -- Push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
 yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;

 yysetstate:
  *yyssp = yystate;

  if (yyss + yystacksize - 1 <= yyssp)
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYSIZE_T yysize = yyssp - yyss + 1;

#ifdef yyoverflow
      {
	/* Give user a chance to reallocate the stack.  Use copies of
	   these so that the &'s don't force the real ones into
	   memory.  */
	YYSTYPE *yyvs1 = yyvs;
	yytype_int16 *yyss1 = yyss;


	/* Each stack pointer address is followed by the size of the
	   data in use in that stack, in bytes.  This used to be a
	   conditional around just the two extra args, but that might
	   be undefined if yyoverflow is a macro.  */
	yyoverflow (YY_("memory exhausted"),
		    &yyss1, yysize * sizeof (*yyssp),
		    &yyvs1, yysize * sizeof (*yyvsp),

		    &yystacksize);

	yyss = yyss1;
	yyvs = yyvs1;
      }
#else /* no yyoverflow */
# ifndef YYSTACK_RELOCATE
      goto yyexhaustedlab;
# else
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
	goto yyexhaustedlab;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
	yystacksize = YYMAXDEPTH;

      {
	yytype_int16 *yyss1 = yyss;
	union yyalloc *yyptr =
	  (union yyalloc *) YYSTACK_ALLOC (YYSTACK_BYTES (yystacksize));
	if (! yyptr)
	  goto yyexhaustedlab;
	YYSTACK_RELOCATE (yyss);
	YYSTACK_RELOCATE (yyvs);

#  undef YYSTACK_RELOCATE
	if (yyss1 != yyssa)
	  YYSTACK_FREE (yyss1);
      }
# endif
#endif /* no yyoverflow */

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;


      YYDPRINTF ((stderr, "Stack size increased to %lu\n",
		  (unsigned long int) yystacksize));

      if (yyss + yystacksize - 1 <= yyssp)
	YYABORT;
    }

  YYDPRINTF ((stderr, "Entering state %d\n", yystate));

  goto yybackup;

/*-----------.
| yybackup.  |
`-----------*/
yybackup:

  /* Do appropriate processing given the current state.  Read a
     look-ahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to look-ahead token.  */
  yyn = yypact[yystate];
  if (yyn == YYPACT_NINF)
    goto yydefault;

  /* Not known => get a look-ahead token if don't already have one.  */

  /* YYCHAR is either YYEMPTY or YYEOF or a valid look-ahead symbol.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      yychar = YYLEX;
    }

  if (yychar <= YYEOF)
    {
      yychar = yytoken = YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yyn == 0 || yyn == YYTABLE_NINF)
	goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  if (yyn == YYFINAL)
    YYACCEPT;

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the look-ahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);

  /* Discard the shifted token unless it is eof.  */
  if (yychar != YYEOF)
    yychar = YYEMPTY;

  yystate = yyn;
  *++yyvsp = yylval;

  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- Do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     `$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];


  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
        case 2:
#line 72 "grammar.y"
    {parse_tree = (yyvsp[(1) - (1)].node);}
    break;

  case 4:
#line 76 "grammar.y"
    {(yyval.node) = cons((yyvsp[(1) - (1)].node),NIL);}
    break;

  case 5:
#line 77 "grammar.y"
    {(yyval.node) = cons((yyvsp[(2) - (2)].node),(yyvsp[(1) - (2)].node));}
    break;

  case 6:
#line 81 "grammar.y"
    {(yyval.node) = new_node(MODULE,(yyvsp[(2) - (3)].node),(yyvsp[(3) - (3)].node));}
    break;

  case 7:
#line 84 "grammar.y"
    {(yyval.node) = new_node(MODTYPE,(yyvsp[(1) - (1)].node),NIL);}
    break;

  case 8:
#line 85 "grammar.y"
    {(yyval.node) = new_node(MODTYPE,(yyvsp[(1) - (4)].node),(yyvsp[(3) - (4)].node));}
    break;

  case 9:
#line 88 "grammar.y"
    {(yyval.node) = NIL;}
    break;

  case 10:
#line 89 "grammar.y"
    {(yyval.node) = cons((yyvsp[(2) - (2)].node),(yyvsp[(1) - (2)].node));}
    break;

  case 24:
#line 107 "grammar.y"
    {(yyval.node) = new_node(IMPLEMENTS,(yyvsp[(2) - (2)].node),NIL);}
    break;

  case 25:
#line 110 "grammar.y"
    {(yyval.node) = new_node(VAR,(yyvsp[(2) - (2)].node),NIL);}
    break;

  case 26:
#line 113 "grammar.y"
    {(yyval.node) = new_node(INPUT,(yyvsp[(2) - (2)].node),NIL);}
    break;

  case 27:
#line 116 "grammar.y"
    {(yyval.node) = new_node(OUTPUT,(yyvsp[(2) - (3)].node),NIL);}
    break;

  case 28:
#line 119 "grammar.y"
    {(yyval.node) = NIL;}
    break;

  case 29:
#line 121 "grammar.y"
    {(yyval.node) = cons(new_node(COLON,(yyvsp[(2) - (5)].node),(yyvsp[(4) - (5)].node)),(yyvsp[(1) - (5)].node));}
    break;

  case 30:
#line 124 "grammar.y"
    {(yyval.node) = new_node(BOOLEAN,NIL,NIL);}
    break;

  case 31:
#line 125 "grammar.y"
    {(yyval.node) = new_node(SCALAR,(yyvsp[(2) - (3)].node),NIL);}
    break;

  case 33:
#line 127 "grammar.y"
    {(yyval.node) = new_node(ARRAY,(yyvsp[(2) - (4)].node),(yyvsp[(4) - (4)].node));}
    break;

  case 34:
#line 128 "grammar.y"
    {(yyval.node) = new_node(PROCESS,(yyvsp[(2) - (2)].node),NIL);}
    break;

  case 36:
#line 132 "grammar.y"
    {(yyval.node) = new_node(MODTYPE,(yyvsp[(1) - (1)].node),NIL);}
    break;

  case 37:
#line 133 "grammar.y"
    {(yyval.node) = new_node(MODTYPE,(yyvsp[(1) - (4)].node),(yyvsp[(3) - (4)].node));}
    break;

  case 38:
#line 136 "grammar.y"
    {(yyval.node) = new_node(TWODOTS,(yyvsp[(1) - (3)].node),(yyvsp[(3) - (3)].node));}
    break;

  case 39:
#line 139 "grammar.y"
    {(yyval.node) = new_node(ISA,(yyvsp[(2) - (2)].node),NIL);}
    break;

  case 40:
#line 142 "grammar.y"
    {(yyval.node) = new_node(INIT,(yyvsp[(2) - (2)].node),NIL);}
    break;

  case 41:
#line 145 "grammar.y"
    {(yyval.node) = new_node(TRANS,(yyvsp[(2) - (2)].node),NIL);}
    break;

  case 42:
#line 148 "grammar.y"
    {(yyval.node) = new_node(INVAR,(yyvsp[(2) - (2)].node),NIL);}
    break;

  case 43:
#line 151 "grammar.y"
    {(yyval.node) = new_node(DEFINE,(yyvsp[(2) - (2)].node),NIL);}
    break;

  case 44:
#line 154 "grammar.y"
    {(yyval.node) = NIL;}
    break;

  case 45:
#line 156 "grammar.y"
    {(yyval.node) = cons(new_node(EQDEF,(yyvsp[(2) - (5)].node),(yyvsp[(4) - (5)].node)),(yyvsp[(1) - (5)].node));}
    break;

  case 46:
#line 159 "grammar.y"
    {(yyval.node) = new_node(ASSIGN,(yyvsp[(2) - (2)].node),NIL);}
    break;

  case 47:
#line 162 "grammar.y"
    {(yyval.node) = NIL;}
    break;

  case 48:
#line 164 "grammar.y"
    {(yyval.node) = new_node(AND,(yyvsp[(1) - (5)].node),new_node(EQDEF,(yyvsp[(2) - (5)].node),(yyvsp[(4) - (5)].node)));}
    break;

  case 50:
#line 168 "grammar.y"
    {(yyval.node) = new_node(NEXT,(yyvsp[(3) - (4)].node),NIL);}
    break;

  case 51:
#line 169 "grammar.y"
    {(yyval.node) = new_node(SMALLINIT,(yyvsp[(3) - (4)].node),NIL);}
    break;

  case 52:
#line 172 "grammar.y"
    {(yyval.node) = new_node(PRINT,(yyvsp[(2) - (2)].node),NIL);}
    break;

  case 53:
#line 173 "grammar.y"
    {(yyval.node) = new_node(SPEC,(yyvsp[(2) - (2)].node),NIL);}
    break;

  case 54:
#line 176 "grammar.y"
    {(yyval.node) = new_node(COMPUTE,(yyvsp[(2) - (2)].node),NIL);}
    break;

  case 55:
#line 179 "grammar.y"
    {(yyval.node) = new_node(FAIRNESS,(yyvsp[(2) - (2)].node),NIL);}
    break;

  case 56:
#line 183 "grammar.y"
    {(yyval.node) = cons(find_atom((yyvsp[(1) - (1)].node)),NIL);}
    break;

  case 57:
#line 184 "grammar.y"
    {(yyval.node) = cons(find_atom((yyvsp[(3) - (3)].node)),(yyvsp[(1) - (3)].node));}
    break;

  case 58:
#line 187 "grammar.y"
    {(yyval.node) = cons(find_atom((yyvsp[(1) - (1)].node)),NIL);}
    break;

  case 59:
#line 188 "grammar.y"
    {(yyval.node) = cons(find_atom((yyvsp[(3) - (3)].node)),(yyvsp[(1) - (3)].node));}
    break;

  case 60:
#line 191 "grammar.y"
    {(yyval.node) = cons((yyvsp[(1) - (1)].node),NIL);}
    break;

  case 61:
#line 192 "grammar.y"
    {(yyval.node) = cons((yyvsp[(3) - (3)].node),(yyvsp[(1) - (3)].node));}
    break;

  case 62:
#line 195 "grammar.y"
    {(yyval.node) = cons((yyvsp[(1) - (1)].node),NIL);}
    break;

  case 63:
#line 196 "grammar.y"
    {(yyval.node) = cons((yyvsp[(3) - (3)].node),(yyvsp[(1) - (3)].node));}
    break;

  case 65:
#line 200 "grammar.y"
    {(yyval.node) = new_node(SELF,NIL,NIL);}
    break;

  case 66:
#line 201 "grammar.y"
    {(yyval.node) = new_node(DOT,(yyvsp[(1) - (3)].node),(yyvsp[(3) - (3)].node));}
    break;

  case 67:
#line 202 "grammar.y"
    {(yyval.node) = new_node(ARRAY,(yyvsp[(1) - (4)].node),(yyvsp[(3) - (4)].node));}
    break;

  case 69:
#line 207 "grammar.y"
    { (yyval.node) = (yyvsp[(2) - (2)].node); }
    break;

  case 70:
#line 209 "grammar.y"
    {(yyvsp[(2) - (2)].node)->left.inttype = -((yyvsp[(2) - (2)].node)->left.inttype); (yyval.node) = (yyvsp[(2) - (2)].node);}
    break;

  case 71:
#line 211 "grammar.y"
    { (yyval.node) = new_node(HIDE,(yyvsp[(2) - (4)].node),(yyvsp[(4) - (4)].node)); }
    break;

  case 72:
#line 212 "grammar.y"
    { (yyval.node) = new_node(EXPOSE,(yyvsp[(2) - (4)].node),(yyvsp[(4) - (4)].node)); }
    break;

  case 79:
#line 220 "grammar.y"
    { (yyval.node) = (yyvsp[(2) - (3)].node); }
    break;

  case 80:
#line 221 "grammar.y"
    { (yyval.node) = new_node(IMPLIES,(yyvsp[(1) - (3)].node),(yyvsp[(3) - (3)].node)); }
    break;

  case 81:
#line 222 "grammar.y"
    { (yyval.node) = new_node(IFF,(yyvsp[(1) - (3)].node),(yyvsp[(3) - (3)].node)); }
    break;

  case 82:
#line 223 "grammar.y"
    { (yyval.node) = new_node(OR,(yyvsp[(1) - (3)].node),(yyvsp[(3) - (3)].node)); }
    break;

  case 83:
#line 224 "grammar.y"
    { (yyval.node) = new_node(AND,(yyvsp[(1) - (3)].node),(yyvsp[(3) - (3)].node)); }
    break;

  case 84:
#line 225 "grammar.y"
    { (yyval.node) = new_node(NOT,(yyvsp[(2) - (2)].node),NIL); }
    break;

  case 85:
#line 226 "grammar.y"
    { (yyval.node) = new_node(EX,(yyvsp[(2) - (2)].node),NIL); }
    break;

  case 86:
#line 227 "grammar.y"
    { (yyval.node) = new_node(AX,(yyvsp[(2) - (2)].node),NIL); }
    break;

  case 87:
#line 228 "grammar.y"
    { (yyval.node) = new_node(EF,(yyvsp[(2) - (2)].node),NIL); }
    break;

  case 88:
#line 229 "grammar.y"
    { (yyval.node) = new_node(AF,(yyvsp[(2) - (2)].node),NIL); }
    break;

  case 89:
#line 230 "grammar.y"
    { (yyval.node) = new_node(EG,(yyvsp[(2) - (2)].node),NIL); }
    break;

  case 90:
#line 231 "grammar.y"
    { (yyval.node) = new_node(AG,(yyvsp[(2) - (2)].node),NIL); }
    break;

  case 91:
#line 232 "grammar.y"
    { (yyval.node) = new_node(AU,(yyvsp[(3) - (6)].node),(yyvsp[(5) - (6)].node)); }
    break;

  case 92:
#line 233 "grammar.y"
    { (yyval.node) = new_node(EU,(yyvsp[(3) - (6)].node),(yyvsp[(5) - (6)].node)); }
    break;

  case 93:
#line 235 "grammar.y"
    { (yyval.node) = new_node(ABU,new_node(AU,(yyvsp[(3) - (7)].node),(yyvsp[(6) - (7)].node)),(yyvsp[(5) - (7)].node)); }
    break;

  case 94:
#line 237 "grammar.y"
    { (yyval.node) = new_node(EBU,new_node(EU,(yyvsp[(3) - (7)].node),(yyvsp[(6) - (7)].node)),(yyvsp[(5) - (7)].node)); }
    break;

  case 95:
#line 238 "grammar.y"
    { (yyval.node) = new_node(EBF,(yyvsp[(3) - (3)].node),(yyvsp[(2) - (3)].node)); }
    break;

  case 96:
#line 239 "grammar.y"
    { (yyval.node) = new_node(ABF,(yyvsp[(3) - (3)].node),(yyvsp[(2) - (3)].node)); }
    break;

  case 97:
#line 240 "grammar.y"
    { (yyval.node) = new_node(EBG,(yyvsp[(3) - (3)].node),(yyvsp[(2) - (3)].node)); }
    break;

  case 98:
#line 241 "grammar.y"
    { (yyval.node) = new_node(ABG,(yyvsp[(3) - (3)].node),(yyvsp[(2) - (3)].node)); }
    break;

  case 99:
#line 242 "grammar.y"
    { (yyval.node) = (yyvsp[(2) - (3)].node); }
    break;

  case 100:
#line 243 "grammar.y"
    { (yyval.node) = new_node(NEXT,(yyvsp[(3) - (4)].node),NIL); }
    break;

  case 101:
#line 244 "grammar.y"
    { (yyval.node) = new_node(PLUS,(yyvsp[(1) - (3)].node),(yyvsp[(3) - (3)].node)); }
    break;

  case 102:
#line 245 "grammar.y"
    { (yyval.node) = new_node(MINUS,(yyvsp[(1) - (3)].node),(yyvsp[(3) - (3)].node)); }
    break;

  case 103:
#line 246 "grammar.y"
    { (yyval.node) = new_node(TIMES,(yyvsp[(1) - (3)].node),(yyvsp[(3) - (3)].node)); }
    break;

  case 104:
#line 247 "grammar.y"
    { (yyval.node) = new_node(DIVIDE,(yyvsp[(1) - (3)].node),(yyvsp[(3) - (3)].node)); }
    break;

  case 105:
#line 248 "grammar.y"
    { (yyval.node) = new_node(MOD,(yyvsp[(1) - (3)].node),(yyvsp[(3) - (3)].node)); }
    break;

  case 106:
#line 249 "grammar.y"
    { (yyval.node) = new_node(EQUAL,(yyvsp[(1) - (3)].node),(yyvsp[(3) - (3)].node)); }
    break;

  case 107:
#line 250 "grammar.y"
    { (yyval.node) = new_node(NOTEQUAL,(yyvsp[(1) - (3)].node),(yyvsp[(3) - (3)].node)); }
    break;

  case 108:
#line 251 "grammar.y"
    { (yyval.node) = new_node(LT,(yyvsp[(1) - (3)].node),(yyvsp[(3) - (3)].node)); }
    break;

  case 109:
#line 252 "grammar.y"
    { (yyval.node) = new_node(GT,(yyvsp[(1) - (3)].node),(yyvsp[(3) - (3)].node)); }
    break;

  case 110:
#line 253 "grammar.y"
    { (yyval.node) = new_node(LE,(yyvsp[(1) - (3)].node),(yyvsp[(3) - (3)].node)); }
    break;

  case 111:
#line 254 "grammar.y"
    { (yyval.node) = new_node(GE,(yyvsp[(1) - (3)].node),(yyvsp[(3) - (3)].node)); }
    break;

  case 112:
#line 255 "grammar.y"
    { (yyval.node) = (yyvsp[(2) - (3)].node); }
    break;

  case 113:
#line 256 "grammar.y"
    { (yyval.node) = new_node(UNION,(yyvsp[(1) - (3)].node),(yyvsp[(3) - (3)].node)); }
    break;

  case 114:
#line 257 "grammar.y"
    { (yyval.node) = new_node(SETIN,(yyvsp[(1) - (3)].node),(yyvsp[(3) - (3)].node)); }
    break;

  case 115:
#line 259 "grammar.y"
    { (yyval.node) = new_node(NOT,new_node(SETIN,(yyvsp[(1) - (3)].node),(yyvsp[(3) - (3)].node)),NIL); }
    break;

  case 116:
#line 261 "grammar.y"
    { (yyval.node) = new_node(SIGMA,new_node(EQUAL,(yyvsp[(3) - (7)].node),(yyvsp[(5) - (7)].node)),(yyvsp[(7) - (7)].node)); }
    break;

  case 117:
#line 264 "grammar.y"
    { (yyval.node) = new_node(MINU,(yyvsp[(3) - (6)].node),(yyvsp[(5) - (6)].node)); }
    break;

  case 118:
#line 265 "grammar.y"
    { (yyval.node) = new_node(MAXU,(yyvsp[(3) - (6)].node),(yyvsp[(5) - (6)].node)); }
    break;

  case 120:
#line 269 "grammar.y"
    {(yyval.node) = new_node(UNION,(yyvsp[(1) - (3)].node),(yyvsp[(3) - (3)].node));}
    break;

  case 125:
#line 278 "grammar.y"
    {(yyval.node)=new_node(TRUEEXP,NIL,NIL);}
    break;

  case 126:
#line 280 "grammar.y"
    {
	          (yyval.node) = new_node(CASE,new_node(COLON,(yyvsp[(1) - (5)].node),(yyvsp[(3) - (5)].node)),(yyvsp[(5) - (5)].node));
	        }
    break;

  case 129:
#line 289 "grammar.y"
    {catch_err(check_spec((yyvsp[(2) - (3)].node)))}
    break;

  case 130:
#line 290 "grammar.y"
    {catch_err(compute_bound((yyvsp[(2) - (3)].node)))}
    break;

  case 131:
#line 291 "grammar.y"
    {catch_err(goto_state((yyvsp[(2) - (3)].node)))}
    break;

  case 132:
#line 292 "grammar.y"
    {catch_err(assign_command((yyvsp[(2) - (5)].node),(yyvsp[(4) - (5)].node)))}
    break;

  case 133:
#line 293 "grammar.y"
    {catch_err(single_step())}
    break;

  case 134:
#line 294 "grammar.y"
    {catch_err(eval_command((yyvsp[(2) - (3)].node)))}
    break;

  case 135:
#line 295 "grammar.y"
    {catch_err(init_command((yyvsp[(2) - (3)].node)))}
    break;

  case 136:
#line 296 "grammar.y"
    {catch_err(fair_command((yyvsp[(2) - (3)].node)))}
    break;

  case 137:
#line 297 "grammar.y"
    {catch_err(trans_command((yyvsp[(2) - (3)].node)))}
    break;

  case 138:
#line 298 "grammar.y"
    {catch_err(reset_command())}
    break;

  case 139:
#line 299 "grammar.y"
    {yyerrok;}
    break;

  case 140:
#line 302 "grammar.y"
    {(yyval.node) = (node_ptr)find_atom((yyvsp[(1) - (1)].node));}
    break;

  case 141:
#line 303 "grammar.y"
    {(yyval.node) = find_node(DOT,(yyvsp[(1) - (3)].node),find_atom((yyvsp[(3) - (3)].node)));}
    break;

  case 142:
#line 306 "grammar.y"
    {(yyval.node) = find_node(DOT,(yyvsp[(1) - (3)].node),find_atom((yyvsp[(3) - (3)].node)));}
    break;


/* Line 1267 of yacc.c.  */
#line 2544 "y.tab.c"
      default: break;
    }
  YY_SYMBOL_PRINT ("-> $$ =", yyr1[yyn], &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);

  *++yyvsp = yyval;


  /* Now `shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */

  yyn = yyr1[yyn];

  yystate = yypgoto[yyn - YYNTOKENS] + *yyssp;
  if (0 <= yystate && yystate <= YYLAST && yycheck[yystate] == *yyssp)
    yystate = yytable[yystate];
  else
    yystate = yydefgoto[yyn - YYNTOKENS];

  goto yynewstate;


/*------------------------------------.
| yyerrlab -- here on detecting error |
`------------------------------------*/
yyerrlab:
  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
#if ! YYERROR_VERBOSE
      yyerror (YY_("syntax error"));
#else
      {
	YYSIZE_T yysize = yysyntax_error (0, yystate, yychar);
	if (yymsg_alloc < yysize && yymsg_alloc < YYSTACK_ALLOC_MAXIMUM)
	  {
	    YYSIZE_T yyalloc = 2 * yysize;
	    if (! (yysize <= yyalloc && yyalloc <= YYSTACK_ALLOC_MAXIMUM))
	      yyalloc = YYSTACK_ALLOC_MAXIMUM;
	    if (yymsg != yymsgbuf)
	      YYSTACK_FREE (yymsg);
	    yymsg = (char *) YYSTACK_ALLOC (yyalloc);
	    if (yymsg)
	      yymsg_alloc = yyalloc;
	    else
	      {
		yymsg = yymsgbuf;
		yymsg_alloc = sizeof yymsgbuf;
	      }
	  }

	if (0 < yysize && yysize <= yymsg_alloc)
	  {
	    (void) yysyntax_error (yymsg, yystate, yychar);
	    yyerror (yymsg);
	  }
	else
	  {
	    yyerror (YY_("syntax error"));
	    if (yysize != 0)
	      goto yyexhaustedlab;
	  }
      }
#endif
    }



  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse look-ahead token after an
	 error, discard it.  */

      if (yychar <= YYEOF)
	{
	  /* Return failure if at end of input.  */
	  if (yychar == YYEOF)
	    YYABORT;
	}
      else
	{
	  yydestruct ("Error: discarding",
		      yytoken, &yylval);
	  yychar = YYEMPTY;
	}
    }

  /* Else will try to reuse look-ahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:

  /* Pacify compilers like GCC when the user code never invokes
     YYERROR and the label yyerrorlab therefore never appears in user
     code.  */
  if (/*CONSTCOND*/ 0)
     goto yyerrorlab;

  /* Do not reclaim the symbols of the rule which action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;	/* Each real token shifted decrements this.  */

  for (;;)
    {
      yyn = yypact[yystate];
      if (yyn != YYPACT_NINF)
	{
	  yyn += YYTERROR;
	  if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYTERROR)
	    {
	      yyn = yytable[yyn];
	      if (0 < yyn)
		break;
	    }
	}

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
	YYABORT;


      yydestruct ("Error: popping",
		  yystos[yystate], yyvsp);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  if (yyn == YYFINAL)
    YYACCEPT;

  *++yyvsp = yylval;


  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", yystos[yyn], yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturn;

/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturn;

#ifndef yyoverflow
/*-------------------------------------------------.
| yyexhaustedlab -- memory exhaustion comes here.  |
`-------------------------------------------------*/
yyexhaustedlab:
  yyerror (YY_("memory exhausted"));
  yyresult = 2;
  /* Fall through.  */
#endif

yyreturn:
  if (yychar != YYEOF && yychar != YYEMPTY)
     yydestruct ("Cleanup: discarding lookahead",
		 yytoken, &yylval);
  /* Do not reclaim the symbols of the rule which action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
		  yystos[*yyssp], yyvsp);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
#if YYERROR_VERBOSE
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
#endif
  /* Make sure YYID is used.  */
  return YYID (yyresult);
}


#line 308 "grammar.y"


