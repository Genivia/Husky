Lazy functional programming with Husky
======================================

- [Husky syntax](#husky-syntax)
- [Definitions](#definitions)
- [Types](#types)
- [Examples](#examples)
- [Functions](#functions)
- [List comprehension](#list-comprehension)
- [Macros](#macros)
- [Special constructs](#special-constructs)
- [Lambdas](#lambdas)
- [Commands](#commands)
- [Gotchas](#gotchas)
- [Installation](#installation)
- [Author](#author)
- [License](#license)

Husky is a lazy functional language similar to Haskell.  Husky implements a
Hindley-Milner-style parametric polymorphic type system, higher-order
functions, argument pattern matching for function specialization, currying,
macros, list comprehension, and monads.

Husky uses NOR (normal order reduction), WHNF (weak head normal form), sharing
(an important lazy evaluation optimization), and lazy constructors to create
infinite "lazy" data structures.

For example, we can create an infinite list of integers, filter the even
numbers, and only pick the first ten even numbers:

    > take(10, filter(even, from(1))).
    [2, 4, 6, 8, 10, 12, 14, 16, 18, 20] :: [num].

Function `from(1)` returns the infinite list `[1, 2, 3, ...]`, `even(n)`
returns `true` if `n` is even, and `filter` retains all even values in the list
using `even` as a filter.

Husky is written in SWI-Prolog using Prolog unification for efficient beta
normal-order reduction of the lambda `A -> B` applied to argument `X`:

    apply(A -> B, X, B) :- !, (var(A) -> A = X; eval(X, V) -> A = V).

The `apply` operation takes a lambda `A -> B` to apply to the unevaluated `X`,
then returns `B` when `A` is a variable.  If `A` is not a variable, then
pattern matching is used by evaluating `X` to `V` and unifying `A` with `V`.

Sharing is implemented internally by using an `eval(X, V)` functor that holds
an (un)evaluated expression `X` and variable `V`.  When `X` is evaluated to a
value, variable `V` is set to that value, thereby sharing the value of `V` to
all uses of `V` (which are of the form of `eval(X, V)`) in an expression.

This reduction method makes Husky run fast, asymptotically as fast as Haskell.
Except that Husky does not optimize tail recursion, meaning that very deep
recursive calls will eventually fail.

Type inference is performed by Prolog inference.  Type rules are expressed as
Prolog clauses for the Husky type inference operator `::`.  These clauses have
a one-to-one correspondence to Post system rules that are often used to define
polymorphic type systems with rules for type inference.  For example, the
polymorphic type of a lambda is defined as a Prolog rule:

    (A -> B) :: Alpha -> Beta :- A :: Alpha, B :: Beta.

This rule infers the type of a lambda as `Alpha -> Beta` if argument `A` is of
type `Alpha` and `B` is of type `Beta`.

The type rule for lambda application (`:`) uses Prolog unification with the
"occurs check" to safely implement the Hindley-Milner-style parametric
polymorphic type system of Husky:

    F:A :: Beta :- !, A :: Alpha, F :: Gamma, unify_with_occurs_check(Gamma, (Alpha -> Beta))

It is that simple!

The Curry-Howard correspondence (the link between logic and computation)
trivially follows by observing that the plain unoptimized beta reduction rule
is the same as the type inference rule for application without the occurs
check:

    apply(F, A, B) :- eval(F, (A -> B)).
    F:A :: Beta :- F :: (Alpha -> Beta), A :: Alpha.

In both rules `A` and its type `Alpha` are unified with the lambda argument to
produce `B` and its type `Beta`.

Because Husky evaluation rules and type inference rules are defined in Prolog,
the implementation is easy to understand and change, for example to add
features, to change the language, and to experiment with type systems.

Husky syntax
------------

Husky syntax follows the usual syntax of arithmetic expressions with functions.
Functions are applied to one or more parenthesized arguments:

    func(arg1, arg2, ...)

Values are Booleans `true` and `false`, numbers, strings (quoted with `"`),
lists written with `[` and `]` brackets, and arbitrary data structures.

At the Husky prompt you can enter expressions which are evaluated and the
answer is returned together with its inferred type.  Global type declarations
and function definitions entered at the command prompt are stored with the
program.  Input may span one or more lines and should end with a period (`.`).

    > 1+2.
    3 :: num

    > x^2 where x := sin(1)-2.
    1.3421894790419853 :: num

    > true /\ false \/ true.
    true :: bool

    > "hello" // "world".
    "helloworld" :: string

    > [1,2,3] ++ [4,5].
    [1, 2, 3, 4, 5] :: [num]

    > (1+2, \ true).
    (3, false) :: (num, bool)

    > x->x+1.
    $0->$0+1 :: num->num

    > f where f(x) := x+1.
    $0->$0+1 :: num->num

    > map(f, [1,2,3]) where f(x) := x+1.
    [2,3,4] :: [num]

    > zip([1, 2, 3], [true, true, false]).
    [(1, true), (2, true), (3, false)] :: [(num, bool)]

Type variables and formal arguments of functions and lambdas are internally
anonymized and replaced by `$i` where `i` is an integer.

Many functions and operators are predefined in Husky, either as built-ins or
as prelude functions, see [Functions](#functions).

In Husky, `v->b` is a lambda (abstraction) with argument `v` and body
expression `b`.  Applications of lambdas are written with a colon (`:`), for
example `(v->v+1):3` applies the lambda `v->v+1` to the value `3` giving `4`.
When applying named functions the usual parenthesized form can be used, for
example `f(3)` to apply `f` to the value `3`.  Also `f:3` is permitted.

Currying of functions and operators is supported.  For example, addition can be
written in functional form `+(x,y)` and `(+):x:y` and even `+(x):y`.  These are
all different representations of the same expression.  This makes Currying
intuitive, for example `+(1)` is the increment function, `*(2)` doubles, and
`/(1)` inverts (note the parameter placement order in this case!).

Lists in Husky are written with brackets, for example`[]` and `[1,2]`.  The
special form `[x|xs]` represents a list with head expression `x` and tail
expression `xs`.  The dot notation `x.xs` is also allowed to represent a list
with head `x` and tail `xs`, where `.` is the list constructor function.

Definitions
-----------

A definition in Husky is written as `LHS := RHS`, where `LHS` is a name or a
function name with parenthesized arguments and `RHS` is an expression.

For example:

    one := 1.
    inc(x) := x + 1.
    hypotenuse(x, y) := sqrt(x^2 + y^2).

Definitions of functions can span more than one `LHS := RHS` pair in which the
definitions should be separated with a semicolon (`;`).  This allows you to
define pattern arguments for function specialization:

    fact(0) := 1;
    fact(n) := n * fact(n - 1).

Multiple definitions of a function typically have constants and data structures
as arguments for which the function has a specialized function body.

A wildcard formal argument `_` is permitted.  For example to define the `const`
function:

    const(x, _) := x.

Types
-----

Types are automatically inferred, like Haskell.  Types can also be explicitly
associated with definitions using the `::` operator.  New named types and
parametric types can be defined.

Husky has three built-in atomic types:

    bool           Booleans
    num            integers, rationals, and floats
    string         strings

- the Boolean type has two values `true` and `false`;
- rationals are written with `rdiv` in the form `numerator rdiv denominator`;
- floats are written conventionally with +/- sign, a period, and exponent;
- strings are sequences of characters enclosed in double quotes (`"`);
- the `nil` constant denotes the so-called "bottom value" (an undefined value)
  and is polymorphic.

Husky has three built-in type constructors:

    [alpha]          a list of elements of type alpha
    (alpha, beta)    a tuple is the product of types alpha and beta
    alpha -> beta    a function mapping elements of type alpha to type beta

New parametric data types and their constructors can be defined as follows:

    MyType :: type.
    Constructor1(arg1, arg2, ..., argm) :: MyType(parm1, parm2, ..., parmn).
    ...
    ConstructorN(arg1, arg2, ..., argk) :: MyType(parm1, parm2, ..., parmn).

Any name can be used to represent a type parameter, even symbols.  Therefore, a
polymorphic list type can be written as `[alpha]` or simply `[*]`.  For
example, the comparison operator `=` has type `(=) :: * -> * -> bool`.

Some examples of named types and parametric types:

    one :: num.
    one := 1.

    inc :: num->num.
    inc := +(1).

    Day :: type.
    Mon :: Day.
    Tue :: Day.
    Wed :: Day.
    Thu :: Day.
    Fri :: Day.
    Sat :: Day.
    Sun :: Day.
    WeekDays :: [Day].
    WeekDays := [Mon,Tue,Wed,Thu,Fri].
    isWeekDay(Mon) := true;
    isWeekDay(Tue) := true;
    isWeekDay(Wed) := true;
    isWeekDay(Thu) := true;
    isWeekDay(Fri) := true;
    isWeekDay(day) := false.
    verify := all(map(isWeekDay, WeekDays)).

    BinTree :: type.
    Leaf :: BinTree(*).
    Node(*, BinTree(*), BinTree(*)) :: BinTree(*).

Examples
--------

    > a := 2.
    DEFINED a::num

    > f(x) := x+1.
    DEFINED f::num->num

    > f(a).
    3 :: num

    % the same function f, now using the colon syntax:
    > f:x := (+):x:1.
    DEFINED f::num->num

    % the same function f, now using currying:
    > f := +(1).
    DEFINED f::num->num

    % In fact, the function definitions are translated into lambda expressions. For
    % example, typing the function name returns its lambda expression:

    > f(a) := a+1.
    DEFINED f::num->num
    > f.
    $0->$0+1 :: num->num

    > plus(x,y) := x+y.
    DEFINED plus::num->num->num
    > plus.
    $0->$1->$0+$1 :: num->num->num

    % A lambda expression can have alternative definitions (of the same type)
    % separated by ';', for example the factorial function:

    % a function with argument specializations:
    > fact(0) := 1;
      fact(n) := n*fact(n-1).
    DEFINED fac::num->num
    > fact.
    0->1;$0->$0*fac($0-1) :: num->num
    > fact(6).
    720 :: num

    % Constants can be used to construct new data types, like BinTree:

    % a BinTree type:
    > BinTree :: type.
    DECLARED BinTree::type.

    % define a type synonym (shortcut macro) for BinTree of num:
    > Numtree == BinTree(num).

    % define the Leaf constant:
    > Leaf :: Numtree.
    DECLARED Leaf::BinTree(num).

    % define the Node constructor:
    > Node(num, Numtree, Numtree) :: Numtree.
    Node(num, BinTree(num), BinTree(num)) :: BinTree(num).

    % Let's try it out by building a tree:
    > Node(3, Node(1, Leaf, Leaf), Node(4, Leaf, Leaf)).
    Node(3, Node(1, Leaf, Leaf), Node(4, Leaf, Leaf)) :: BinTree(num)

Functions
---------

Built-in operators and functions are defined in prelude.sky:

    - x         unary minus (can also use 'neg' for unary minus, e.g. for currying)
    x + y       addition
    x - y       subtraction
    x * y       multiplication
    x / y       division
    x rdiv y    rational division with "infinite" precision
    x div y     integer division
    x mod y     modulo
    x ^ y       power
    min(x,y)    minimum
    max(x,y)    maximum
    x = y       equal (structural comparison)
    x <> y      not equal (structural comparison)
    x < y       less (num and string)
    x <= y      less or equal (num and string)
    x > y       greater (num and string)
    x >= y      greater or equal (num and string)
    \ x         logical not
    x /\ y      logical and
    x \/ y      logical or
    gcd(x, y)   GCD
    lcm(x, y)   LCM
    fac(x)      factorial
    fib(x)      Fibonacci
    id(x)       identity (returns x)
    abs(x)      absolute value
    sin(x)      sine
    cos(x)      cosine
    tan(x)      tangent
    asin(x)     arc sine
    acos(x)     arc cosine
    atan(x)     arc tangent
    exp(x)      e^x
    log(x)      natural logarithm (nil when x<0)
    sqrt(x)     root (nil when x<0)
    x // y      string concatenation
    (x,y)       tuple (note: tuple constructors are strict, not lazy)
    x.xs        a list with head x and tail xs (list constructors are lazy)
    [x|xs]      same as above: a list with head x and tail xs
    # xs        list length
    xs ? n      element of list xs at index n >= 1
    hd(xs)      head element of list xs (nil when x=[])
    tl(xs)      tail element of list xs (nil when x=[])
    init(xs)    init of xs without the last element
    last(xs)    last element of xs
    xs ++ ys    list concatenation
    xs \\ ys    list subtraction
    x is_in xs  list membership check (positive test)
    x not_in xs list membership check (negative test)
    fst((x,y))  first (=x)
    snd((x,y))  second (=y)
    even(x)     true when x is even
    odd(x)      true when x is odd

    num(s)      convert string s to number (nil when s is not numeric)
    str(x)      convert number x to string
    s2ascii(s)  convert string s to list of ASCII codes
    ascii2s(xs) convert list xs of ASCII codes to string

    read        prompts user and returns input string
    write(x)    display x (returns x)
    writeln(x)  display x '\n' (returns x)
    getc        returns single input char in ASCII
    putc(x)     display character of ASCII code x (returns x)

    map         map(f, xs) maps f onto xs [f(x1), f(x2), ..., f(xk)]
    filter      filter(p, xs) yields elements of xs that fulfill p
    foldl       foldl(f, x, xs) = f(x, ... f(f(f(x1, x2), x3), x4), ...)
    foldr       foldr(f, x, xs) = f(... f(xk-2, f(xk-1, f(xk, x))) ... )
    foldl1      foldl1(f, xs) foldl over non-empty list
    foldr1      foldr1(f, xs) foldr over non-empty list
    scanl       scanl left scan
    scanr       scanr right scan
    all         all(p, xs) = true if all elements in xs fulfill p
    any         any(p, xs) = true if any element in xs fulfills p
    concat      concat list of lists
    zip         zip(xs, ys) zips two lists
    unzip       unzip(xys) unzips list of tuples
    zipwith     zipwith(f, xs, ys) zips two lists using operator f
    until       until(p, f, x) applies f to x until p(x) holds
    iterate     iterate(f, x) = [x, f(x), f(f(x)), f(f(f(x))), ... ]
    from        from(n) = [n, n+1, n+2, ...]
    repeat      repeat(x) produces [x,x,x,...]
    replicate   replicate(n, x) generates list of n x's
    cycle       cycle(xs) generates cyclic list xs ++ xs ++ ...
    drop        drop(n, xs) drops n elements from xs
    take        take(n, xs) takes n elements from xs
    dropwhile   dropwhile(p, xs) drops first elements fulfilling p from xs
    takewhile   takewhile(p, xs) takes first elements fulfilling p from xs
    reverse     reverse list
    f @ g       function composition ("f after g")
    twiddle     twiddle operands twiddle(f:x, y) means f(y, x)
    flip        flip(f, x, y) flips operands to apply f(y, x)
    curry       curry function curry(f, x, y) := f((x, y))
    uncurry     uncurry function uncurry(f, (x, y)) := f(x, y)

List comprehension
------------------

A list comprehension has the following form:

    [ expr | qual; qual; ...; qual ]

where the qualifiers are generators of the form `x <- xs` or guards over the
free variables.  Guards over one or more generator variables must be placed to
the right of the generator, i.e. variable scoping applies to the right.

For example:

    [ x^2 | x <- 1..10; even(x) ].

    [ (a,b) | a <- 1..3; b <- 1..a ].

    [ (a,b) | a <- 1..5; odd(a); b <- 1..a; a mod b = 0 ].

Macros
------

Macros are defined with `==` to serve as shorthands for expressions and types:

    StartValue   == 0.
    Address      == num.
    MachineState == Address->num.
    NumTree      == BinTree(num).

Macro expansion is structural: names, functions, lists, and other syntactic
structures can be defined as macros with parameters, i.e. macros support
pattern matching for macro specialization.

In fact, list comprehension syntax is entirely implemented by recursive macro
expansion into `concat`, `map`, and `filter` (defined in prelude.sky):

    [ f | x <- xs; p; y <- ys; r ] == concat(map(x -> [ f | y <- ys; r ], filter(x -> p, xs))).
    [ f | x <- xs; p; y <- ys    ] == concat(map(x -> [ f | y <- ys    ], filter(x -> p, xs))).

    [ f | x <- xs; y <- ys; r ] == concat(map(x -> [ f | y <- ys; r ], xs)).
    [ f | x <- xs; y <- ys    ] == concat(map(x -> [ f | y <- ys    ], xs)).

    [ f | x <- xs; p; q; r ] == [ f | x <- xs; p /\ q; r ].
    [ f | x <- xs; p; q    ] == [ f | x <- xs; p /\ q    ].

    [ x | x <- xs; p ] == filter(x -> p, xs).
    [ f | x <- xs; p ] == map(x -> f, filter(x -> p, xs)).

    [ x | x <- xs ] == xs.
    [ f | x <- xs ] == map(x -> f, xs).

The monad `do` operator (defined in monads.sky):

    do(x := y; z) == do(z) where x := y.
    do(x <- y; z) == y >>= (x -> do(z)).
    do(z) == z.

Note that macros do not evaluate arguments!  Only syntactical structures can be
pattern matched.  New syntax can be introduced by declaring prefix, infix, and
postfix opertors, see [Commands](#commands).

Special constructs
------------------

    if b then x else y      a conditional expression

    x where y := z          each y in x is replaced by z

    fix(f)                  the fixed-point Y-combinator (fix:f = f:(fix:f))

    (let defs in val)       the 'let' construct (use parenthesis!)

    case val of (const1 -> val1; const2 -> val2; ... constk -> valk)
                            the 'case' construct (translated to lambdas)

For example:

    test := (let f := ^(2); start := 1; end := 10 in map(f, start..end)).

    case n of (1 -> "one"; 2 -> "two"; 3 -> "three")

Lambdas
-------

A lamba (abstraction) is written as `v->b`.  When a lambda has alternatives as
arguments, i.e. a set of argument choices such as constants and partial data
structures, then the alternatives should be separated by semicolons (`;`).

Functions with alternative formal arguments are automatically translated to the
corresponding lambda abstractions.

    v->b                    lambda abstraction
    (v->b):a                application of a lambda to an argument
    (v->b; w->c):a          application of a lambda with specializations

Commands
--------

    listing.                lists the contents of the loaded program(s)
    bye.                    close session
    reset.                  soft reset
    trace.                  trace on
    notrace.                trace off
    profile.                collect execution profile stats
    noprofile.              profile off
    save.                   create standalone Husky executable
    load "file".            load file
    save "file".            save listing to file
    :- Goal.                execute Prolog Goal
    remove name.            remove name from definitions
    prefix (op).            declare prefix operator op
    postfix (op).           declare postfix operator op
    infix (op).             declare non-associative infix operator op
    infixl (op).            declare left associative infix operator op
    infixr (op).            declare right associative infix operator op
    num prefix (op).        declare prefix operator op with precedence num
    num postfix (op).       declare postfix operator op with precedence num
    num infix (op).         declare non-associative infix operator op w. prec. num
    num infixl (op).        declare left associative infix operator op w. prec. num
    num infixr (op).        declare right associative infix operator op w. prec. num

Gotchas
-------

- Patterns in function arguments may consist of (parameterized) constants,
  empty list `[]`, `x.xs` non-empty list with head `x` and tail `xs`, and
  tuples `(x,y)`.  These should not be nested:

      BAD:
      f((x,y).xs) := ...

      GOOD:
      f(p.xs) := ... where (x,y) := p.

      BAD:
      f(BinTree(BinTree(left, right), rest)) := ...

      GOOD:
      f(BinTree(tree, rest)) := ...
              where left := f(tree)
              where right := g(tree)
              where f(BinTree(l, r)) := l
              where g(BinTree(l, r)) := r.

- The scope of the `where` construct is limited to its left-hand side.
  Therefore, it does not support recursive definitions:

      BAD:
      ... f(x) ... where f(n) := ... f(n-1) ...

  use the `fix` operator instead:

      GOOD:
      ... fix(f, x) ... where f(ff, n) := ... ff(n-1) ...

- When using tuples in `where`, be aware that tuple constructors are strict:

      x+1 where (x,y) := (1,write("abc");

  which displays "abc" even though `y` is not used, because tuple members are
  evaluated.

- There must be a space between operators, otherwise the system is not able to
  parse the expression.  For example:

      x\/\y           should be written         x\/ \y
      x+#l            should be written         x+ #l
      x*-y            should be written         x* -y
      x<-y            should be written         x< -y

- Parenthesization follows the Prolog syntax, so `f(x,y)` works, but `f(x)(y)`
  causes a syntax error.  Instead, use colons, e.g. `f:x:y` or a mixed form
  such as `f(x):y`.

- There cannot be a space after the dot (`.`) operator, otherwise the system
  considers the input line has ended. In this case, use parenthesis.

Installation
------------

Install SWI-Prolog 8.2.1 or greater from <https://www.swi-prolog.org>.

Then clone Husky with git:

    $ git clone https://github.com/Genivia/husky

Run `swipl` then load Husky and run the `husky` interpreter:

    $ swipl
    ?- [husky].
    :- husky.

After starting Husky, load any one of the example .sky files with:

    > load "examples/<filename>".

To delete examples from memory and reset Husky to system defaults:

    > reset.

To create a stand-alone executable, run `swipl' and enter:

    $ swipl
    :- [husky].
    :- husky.
    > save.
    > bye.

This creates the `husky' executable with the prelude functions preloaded.

Husky source files:

    README.md             this file
    husky.pl              the Husky interpreter
    prelude.sky           built-in definitions

Husky program examples:

    palindrome.sky        palindrome
    btree.sky             binary trees
    clientserver.sky      client-server stream example
    combinators.sky       SKI combinator calculus
    cr.sky                Chains of Recurrences algebra
    hamming.sky           the Hamming problem
    hangman.sky           a simple hangman game
    matrix.sky            matrix and vector operations
    monads.sky            monads a-la Haskell
    primes.sky            primes
    qsort.sky             quicksort
    queens.sky            the queens problem
    semantics.sky         denotational semantics example

Author
------

Husky is created by Prof. Robert A. van Engelen, engelen@acm.org.

License
-------

Open source GPL (GNU public license).
