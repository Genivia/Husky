%       husky.pl
%
%       Husky: a Lazy Functional Language
%
%       Implements typed lambda calculus:
%         NOR + WHNF + sharing + lazy constructors + polymorphic type system
%       and:
%         higher-order functions + type synonyms + argument pattern matching
%         + macros + monads
%
%       This interpreter requires SWI-Prolog
%
%       Usage:
%       $ swipl
%       :- [husky].
%       :- husky.
%       > 1+2.
%
%       Releases of Husky (aka Monica)
%       1.0  2/16/2001  first non-beta version
%       1.1  5/16/2008  updated, fixed 'where' parsing scope
%       1.2  5/25/2008  speed and usability enhancements
%       2.1  5/27/2008  faster, a few fixes, and macro expansion
%       2.2  3/30/2009  several minor improvements
%       2.3  4/07/2009  much faster, improved sharing implementation, added
%                       'let', changed 'in' to 'is_in' and added 'not_in'
%       2.4  4/19/2009  added list comprehensions as macros in prelude.sky
%       2.5 11/22/2009  compatible with SWI Prolog 5.10.4
%       2.6  8/31/2020  compatible with SWI Prolog 8.2.1
%
%       License: GNU Public License (GPL)
%       Author (c) 1999-2020: Robert A. van Engelen

:- module(husky, [husky/0, husky/1, husky/2, repl/0]).

:- use_module(
        [ library(check),
          library(lists),
          library(qsave),
          library(readutil),
          library(statistics)
        ]).

%       Set SWI-Prolog flags

:-      set_prolog_flag(allow_dot_in_atom, true),
        set_prolog_flag(back_quotes, symbol_char),
        set_prolog_flag(character_escapes, false),
        set_prolog_flag(allow_variable_name_as_functor, true),
        set_prolog_flag(optimise, true),
        set_prolog_flag(print_write_options, [module(husky), quoted(true)]),
        set_prolog_flag(history, 100).

%       Set operator precedences and associativities

set_ops :-
        op(1098,  fx, husky:[prefix, postfix, infix, infixl, infixr]),
        op(1098, xfx, husky:[prefix, postfix, infix, infixl, infixr]),
        op(974,  xfx, husky:[==]),
        op(972,  yfx, husky:[where]),
        op(970,  xfy, husky:[:=, ::, ->]),
        op(950,  yfx, husky:[//]),
        op(770,  yfx, husky:[\/]),
        op(760,  yfx, husky:[/\]),
        op(750,   fy, husky:[\]),
        op(700,  xfx, husky:[=, <>, <, <=, >, >=]),
        op(600,  yfx, husky:[min, max]),
        op(400,  yfx, husky:[div, mod]),
        op(110,  yfx, husky:[:]),
        op(100,  xfy, husky:['.']),
        op(100,   fx, husky:[remove, load, save]).

:-      set_ops.

%       husky/0
%       Start a new Husky REPL and perform a soft reset

husky :-
        pragma(reset),
        format('~nWelcome to Husky 2.6~nType "help." for help, "bye." to exit.~n'),
        repl.

%       repl/0
%       Read-evaluate-print loop

repl :-
        repeat, read_history(history, '!history', [module(husky), end_of_file], '> ', Term, Bindings),
                husky(Term, Bindings),
                Term == bye, !.

%       husky(+Term, +Bindings)
%       Handle Prolog directives of the form :- Goal.
%       Binds all Prolog variables to their corresponding atom forms with
%       checklist/2 on read_history Bindongs, then invokes Husky with the
%       specified Term argument that is now a ground term.

husky(V          ,  Bindings) :- var(V), !, checklist(call, Bindings), husky(V).
husky(infix     F, _Bindings) :- nonvar(F), !, op(450, xfx, F).
husky(infixl    F, _Bindings) :- nonvar(F), !, op(450, yfx, F).
husky(infixr    F, _Bindings) :- nonvar(F), !, op(450, xfy, F).
husky(P infix   F, _Bindings) :- nonvar(F), !, op(P,   xfx, F).
husky(P infixl  F, _Bindings) :- nonvar(F), !, op(P,   yfx, F).
husky(P infixr  F, _Bindings) :- nonvar(F), !, op(P,   xfy, F).
husky(prefix    F, _Bindings) :- nonvar(F), !, op(100,  fy, F).
husky(P prefix  F, _Bindings) :- nonvar(F), !, op(P,    fy, F).
husky(postfix   F, _Bindings) :- nonvar(F), !, op(100, yf,  F).
husky(P postfix F, _Bindings) :- nonvar(F), !, op(P,   yf,  F).
husky(:- G,        _Bindings) :- nonvar(G), !, G.
husky(Term,         Bindings) :- checklist(call, Bindings), husky(Term).

%       husky(+Term)
%       Interpret Husky pragmas, evaluate Term and print result

husky(Term) :-
        pragma(Term), !.
husky(Term) :-
        flag(reductions, _, 0),
        flag(funargs, F, 1),
        compile(Term, Expr), !,
        flag(funargs, _, F),
        type(Expr, Type), !,
        share(Expr, Expr1),
        decompile(Type, Type1),
        (       flag(profiling, 1, 1)
        ->      profile(show(Expr1))
        ;       show(Expr1)
        ),
        write(' :: '),
        show(Type1),
        flag(reductions, N, 0),
        (       N == 0
        ;       format(' evaluated in ~p reduction steps', [N])
        ),
        nl, !.

%       pragma(+Term)
%       If Term is a pragma, then execute it; otherwise fail.

pragma(bye).
pragma(end_of_file).
pragma(reset) :-
        retractall(macro(_, _)),
        fail.
pragma(reset) :-
        clause(A := _, true, Ref1),
        recorded(A, mode(_, _), Ref2),
        erase(Ref1),
        erase(Ref2),
        fail.
pragma(reset) :-
        current_key(A),
        atom(A),
        recorded(A, mode(_, _), Ref),
        erase(Ref),
        fail.
pragma(reset) :- !,
        set_ops,
        husky(load "prelude").
pragma(save) :-
        qsave_program('Husky', [goal = true, toplevel = repl, op = save]), !.
pragma(remove F) :-
        recorded(F, mode(_, _), Ref),
        erase(Ref),
        fail.
pragma(remove F) :-
        clause(F := _, true, Ref),
        erase(Ref),
        fail.
pragma(remove _) :- !.
pragma(profile) :-
        flag(profiling, _, 1).
pragma(noprofile) :-
        flag(profiling, _, 0).
pragma(trace) :-
        ( retract(apply(_, _, _) :- (format(_, _), _)); true ),
        asserta(apply(X, Y, _) :- (format('~N{ APPLY ~p TO ~p }~n', [X, Y]), flag(reductions, N, N+1), fail)).
pragma(notrace) :-
        retract(apply(_, _, _) :- (format(_, _), _)).
pragma(notrace) :- !.
pragma(help) :-
        shell("more README.md").
pragma(listing) :-
        format('%%%% MACROS:~n~n'),
        macro(A, M),
        decompile(A == M, D),
        format('~p .~n~n', [D]),
        fail.
pragma(listing) :-
        format('%%%% CONSTANTS:~n~n'),
        current_key(A),
        atom(A),
        recorded(A, mode(T, const)),
        decompile(A :: T, D),
        format('~p .~n~n', [D]),
        fail.
pragma(listing) :-
        format('%%%% DEFINITIONS:~n~n'),
        clause(A := B, true),
        recorded(A, mode(T, _)),
        decompile(A := B, D),
        decompile(T, T1),
        format('~p .~n~p .~n~n', [A :: T1, D]),
        fail.
pragma(listing).
pragma(FAs == B) :-
        FAs =.. [F | As],
        compile_macro_head(As, [], Xs, Env),
        compile_macro_body(B, Env, M),
        FXs =.. [F | Xs],
        functor(FXs, F, N),
        functor(FYs, F, N),
        (       ( macro(FYs, K), FXs =@= FYs, (FXs == M) \=@= (FYs == K) )
        ->      format('Macro ~p already defined~n', [FAs]),
                fail
        ;       assert(macro(FXs, M))
        ).
pragma(A :: T) :-
        flag(funargs, F, 0),
        compile(A :: T, A1 :: T1),
        flag(funargs, _, F),
        (       recorded(A1, mode(T2, M), Ref1)
        ->      erase(Ref1),
                (       T1 =@= T2
                ->      true
                ;       clause(A1 := _, true)
                ->      format('ERROR: type ~p conflicts with definition of ~p~n', [T, A]),
                        fail
                ;       true
                )
        ;       true
        ),
        recorda(A1, mode(T1, M)),
        decompile(T1, T3),
        format('~N{ DECLARED ~p }~n', [A1 :: T3]).
pragma(D) :-
        where(D, W),
        define(W).

%       where(+Def, -Def1)
%       Rewrite the 'where' scopes to correct precedence conflict with :=

where(W; R,           V; Q            ) :- where(W, V), !, where(R, Q).
where(A := B where C, A := (B where D)) :- !, where(C, D).
where(W      where C, A := (B where C)) :- !, where(W, A := B).
where(A := B,         A := B).

%       define(+Def)
%       Called by pragma/1. Def is a pair LHS := RHS

define(D) :-
        flag(funargs, F, 1),
        compile(D, L),
        flag(funargs, _, F),
        def(L), !.
define(D) :-
        format('Error in definition ~p~n', [D]).

def(L; Ls) :- !,
        def(L), !,
        def(Ls).
def(A := B) :-
        (       recorded(A, mode(T, M), Ref)
        ->      (       (M == const)
                ->      format('Cannot redefine named constant ~p~n', [A]),
                        fail
                ;       true
                )
        ;       recorda(A, mode(T, def), Ref)
        ), !,
        type(B, T1),
        erase(Ref),
        (       T = T1
        ->      recorda(A, mode(T, def)),
                (       clause(A := _, true, Ref2)
                ->      erase(Ref2)
                ;       true
                ),
                share(B, B1),
                assert(A := B1),
                decompile(T1, T2),
                format('~N{ DEFINED ~p }~n', [A :: T2])
        ;       decompile(T1, T2),
                format('ERROR: type inconsistency, cannot define ~p~n', [A :: T2])
        ).

%       decompile(+Expr, -Term)
%       Decompile a lambda expression into readable form

decompile(Expr, Term) :-
        copy_term(Expr, Expr1),
        flag(varno, _, 0),
        decomp(Expr1, Term).

decomp(V, V) :-
        var(V), !,
        flag(varno, N, N+1),
        V = '$'(N).
decomp(eval(_, X), Y) :-
        nonvar(X), !,
        decomp(X, Y).
decomp(eval(X, _), Y) :- !,
        decomp(X, Y).
decomp(T :: _, S) :- !,
        decomp(T, S).
decomp(F: A, X) :- !,
        decomp(F, G),
        decomp(A, B),
        (       (       G = (_ -> _)
                ;       G = eval(_ -> _, _)
                ;       G = (_ ; _)
                ;       G = eval(_ ; _, _)
                ;       G = (_ : _)
                ;       G = '$'(_)
                )
        ->      X = (G: B)
        ;       G =.. L,
                append(L, [B], L1),
                X =.. L1
        ).
decomp([H | T], [X | Y]) :- !,
        decomp(H, X), !,
        decomp(T, Y).
decomp([], []) :- !.
decomp(FAs, FBs) :- !,
        FAs =.. [F | As],
        decomp(As, Bs),
        FBs =.. [F | Bs].
decomp(A, A).

%       show(+Expr)
%       Decompile and evaluate Expr on demand and show results.

show(X) :-
        flag(varno, _, 0),
        eval(X, Y),
        copy_term(Y, V),
        (       functor(V, '.', 2)
        ->      write('['),
                show_list(V),
                write(']')
        ;       show(V, T),
                out(T)
        ), !.

show_list([X | Xs]) :-
        show(X, Y),
        out(Y),
        eval(Xs, Ys),
        (       (Ys == [])
        ->      true
        ;       write(', '),
                show_list(Ys)
        ).
show_list([]).

%       show(+Expr, -Term)
%       Similar to decompile/2, but evaluates lazy constructors to show
%       evaluated result.

show(V, V) :-
        var(V), !,
        flag(varno, N, N+1),
        V = '$'(N).
show(eval(_, Y), Y) :-
        nonvar(Y), !.
show(eval(X, Y), Z) :- !,
        eval(X, Y),
        show(Y, Z).
show(T :: _, S) :- !,
        decomp(T, S).
show(F: A, X) :- !,
        show_app(F: A, X).
show([H | T], [X | Y]) :- !,
        show(H, X),
        eval(T, Ts), !,
        show(Ts, Y).
show([], []) :- !.
show(A; B, X; Y) :- !,
        decomp(A, X),
        decomp(B, Y).
show(A -> B, X -> Y) :- !,
        decomp(A, X),
        decomp(B, Y).
show(neg, -) :- !.
show(A, A) :-
        atomic(A), !.
show(FAs, FBs) :- !,
        functor(FAs, F, N),
        functor(FBs, F, N),
        FAs =.. [F | As],
        FBs =.. [F | Bs], !,
        show(As, Bs).

show_app(FA, X) :-
        eval(FA, Y),
        (       Y = (G:A)
        ->      show(A, B),
                (       ( G = (_ -> _) ; G = eval(_ -> _, _) )
                ->      decomp(G:B, X)
                ;       ( G = (_ ; _) ; G = eval(_ ; _, _) )
                ->      X = incomplete_lambda_choice_application_error(FA)
                ;       show(G, H),
                        H =.. L,
                        append(L, [B], L1),
                        X =.. L1
                )
        ;       show(Y, X)
        ).

out(X) :-
        functor(X, F, 1),
        current_op(P, A, F),
        P >= 1000,
        memberchk(A, [fx, fy, xf, yf]), !,
        format('(~p)', X).
out(X) :-
        functor(X, F, 2),
        current_op(P, A, F),
        P >= 1000,
        memberchk(A, [xfx, xfy, yfx]), !,
        format('(~p)', X).
out(X) :-
        print(X),
        flush_output.

%       compile(+Term, -Expr)
%       Compile a term into a lambda expression. Apply alpha conversion etc.
%       The 'funargs' flag determines the handling of arguments, where
%       funargs=1 sets function argument parsing, otherwise type template-type
%       parsing is used, e.g. to support T(alpha,alpha) :: alpha

compile(Term, Expr) :-
        expand(Term, Expanded),
        catch(compile(Expanded, [], Expr), compile_error, true), !.
compile(Term,_Expr) :-
        format('Compilation error in ~p~n', [Term]),
        fail.

expand(V,               V) :- var(V), !.
expand(X,               Z) :- macro(X, Y), !, expand(Y, Z).
expand(A,               A) :- atomic(A), !.
expand([X | Xs], [Y | Ys]) :- !, expand(X, Y), expand(Xs, Ys).
expand(FAs,           FCs) :- FAs =.. Xs, expand(Xs, Ys), FBs =.. Ys, ((FAs == FBs) -> FCs = FBs; expand(FBs, FCs)).

%       split(+AdotB, -A, -B)
%       Split atom with a dot into atoms A and B to work around the SWI-Prolog
%       dict interpretation of dot with set_prolog_flag(allow_dot_in_atom, true)

split(AdotB, A, B) :-
        atom(AdotB),
        atom_codes(AdotB, ABs),
        append(As, [46 | Bs], ABs), !,
        As \= [],
        Bs \= [],
        atom_codes(A, As),
        atom_codes(B, Bs).
  
compile($,                 _Env,        _) :- !, free_var.
compile([],                _Env,       []) :- !.
compile([T | Ts],           Env, [X | Xs]) :- !, compile(T, Env, X), !, compile(Ts, Env, Xs).
compile((T := S; R),        Env,        X) :- !, compile_def((T := S; R), Env, D), transform(D, X).
compile((T, S),             Env,   (X, Y)) :- !, compile(T, Env, X), !, compile(S, Env, Y).
compile((T; S),             Env,   (X; Y)) :- !, compile(T, Env, X), !, compile(S, Env, Y).
compile((T: S),             Env,   (X: Y)) :- !, compile(T, Env, X), !, compile(S, Env, Y).
compile(- T,                Env,   neg: X) :- !, compile(T, Env, X).
compile(T := S,             Env,        X) :- !, compile_def(T := S, Env, D), transform(D, X).
compile(T :: S,             Env, X1 :: Y1) :- !, compile_fun(T, Env, X, Env1), compile_arg(S, Env1, Y, _), transform(X := Y, X1 := Y1).
compile(T -> S,             Env,   X -> Y) :- !, compile_arg(T, Env, X, Env1), compile(S, Env1, Y).
compile(T where S,          Env,      X:Y) :- compile_def(S, Env, D), transform(D, F := Y), !, compile(F -> T, Env, X).
compile(_ where _,         _Env,        _) :- !, format('Invalid where~n'), fail.
compile(AdotB,              Env, [X | Xs]) :- split(AdotB, A, B), !, compile(A, Env, X), compile(B, Env, Xs).
compile(A,                  Env,        X) :- atom(A), memberchk(A = X, Env), !.
compile(A,                 _Env,        A) :- atomic(A), !.
compile(AdotBAs,            Env,        X) :- AdotBAs =.. [AdotB | As], split(AdotB, A, B), !, BAs =.. [B | As], compile([A | BAs], Env, X).
compile(FAs,                Env,        X) :- !, FAs =.. List, cons(List, Cons), compile(Cons, Env, X).

compile_def((A; B), Env, (X; Y)) :- compile_def(A, Env, X), !, compile_def(B, Env, Y).
compile_def(A := B, Env, X := Y) :- compile_fun(A, Env, X, Env1), !, compile(B, Env1, Y).
compile_def(X,     _Env,      _) :- format('Illegal definition ~p~n', X), throw(compile_error).

compile_fun($,     _Env, _,         _) :- !, free_var.
compile_fun(F: A,   Env, G: X,   Env2) :- !, compile_arg(A, Env, X, Env1), !, compile_fun(F, Env1, G, Env2).
compile_fun((F, G), Env, (X, Y), Env2) :- compile_fun(F, Env, X, Env1), !, compile_fun(G, Env1, Y, Env2).
compile_fun(F,      Env, F,       Env) :- atomic(F), !, atom(F).
compile_fun(FAs,    Env, G,      Env1) :- FAs =.. List, cons(List, Cons), !, compile_fun(Cons, Env, G, Env1).

compile_arg(V,       Env, V,           Env) :- var(V), !.
compile_arg([],      Env, [],          Env) :- !.
compile_arg([A],     Env, [X],        Env1) :- !, compile_arg(A, Env, X, Env1).
compile_arg([A | B], Env, [X | Y],    Env1) :- atom(B), !, compile_arg(A, [B = Y | Env], X, Env1).
compile_arg((A, B),  Env, (X, Y),     Env2) :- compile_arg(A, Env, X, Env1), compile_arg(B, Env1, Y, Env2).
compile_arg((A; B),  Env, (X; Y),     Env2) :- compile_arg(A, Env, X, Env1), compile_arg(B, Env1, Y, Env2).
compile_arg((F: A),  Env, (G: X),     Env2) :- compile_arg(F, Env, G, Env1), compile_arg(A, Env1, X, Env2).
compile_arg(A -> B,  Env, X -> Y,     Env2) :- compile_arg(A, Env, X, Env1), compile_arg(B, Env1, Y, Env2).
compile_arg(A,       Env, A,           Env) :- constant(A), !.
compile_arg(AdotB,   Env, [X | Y],    Env1) :- split(AdotB, A, B), !, compile_arg(A, [B = Y | Env], X, Env1).
compile_arg(A,       Env, X,           Env) :- atom(A), flag(funargs, 0, 0), memberchk(A = X, Env), !.
compile_arg(A,       Env, X, [A = X | Env]) :- atom(A), !.
compile_arg(FAs,     Env, Cons1,      Env1) :- FAs =.. List, cons(List, Cons), compile_arg(Cons, Env, Cons1, Env1).

compile_macro_head($,       _Env,        _,         _Env1) :- !, free_var.
compile_macro_head([A | As], Env, [X | Xs],          Env2) :- compile_macro_head(A, Env, X, Env1), !, compile_macro_head(As, Env1, Xs, Env2).
compile_macro_head([],       Env,       [],           Env) :- !.
compile_macro_head(A,        Env,        X,           Env) :- atom(A), memberchk(A = X, Env), !.
compile_macro_head(A,        Env,        X, [A = X | Env]) :- atom(A), !.
compile_macro_head(A,        Env,        A,           Env) :- atomic(A), !.
compile_macro_head(FAs,      Env,      FXs,          Env1) :- FAs =.. [F|As], compile_macro_head(As, Env, Xs, Env1), FXs =.. [F|Xs].

compile_macro_body($,       _Env,        _) :- !, free_var.
compile_macro_body([A | As], Env, [X | Xs]) :- compile_macro_body(A, Env, X), !, compile_macro_body(As, Env, Xs).
compile_macro_body([],      _Env,       []) :- !.
compile_macro_body(A,        Env,        X) :- atom(A), memberchk(A = X, Env), !.
compile_macro_body(FAs,      Env,      FXs) :- FAs =.. [F|As], compile_macro_body(As, Env, Xs), FXs =.. [F|Xs].

transform(X, Z) :- group(X, $, Y), !, transform(Y, Z).
transform(X, X).

group((F:A := B; R), $,                Y) :- !, collect((F:A := B; R), L, S), !, group(S, L, Y).
group((F:A := B; R), X,           (X; Y)) :- !, collect((F:A := B; R), L, S), !, group(S, L, Y).
group(F:A := B,      $,      F := A -> B) :- !.
group(F:A := B,      X, (X; F := A -> B)).
group($,             X,                X).

collect((F:A := B; R), F := L, S) :- collect(R, F := A -> B, L, S).

collect((F:A := B; R), G := X, (X; L),      S) :- F =@= G, unify_with_occurs_check(F, G), !, collect(R, G := A -> B, L, S).
collect(F:A := B,      G := X, (X; A -> B), $) :- F =@= G, unify_with_occurs_check(F, G), !.
collect(R,             _ := L, L,           R).

cons([X | Xs], Cons) :- cons(Xs, Cons, X).

cons([X | Xs], Cons, ConsSofar) :- !, cons(Xs, Cons, ConsSofar:X).
cons([],       Cons,      Cons).

%       share(+X, -Z)
%       Insert eval/2 constructs in lambda body to share argument results.
%       More eval/2 constructs will be inserted than absolutely necessary,
%       because the "flow" of the program is unknown, i.e. consider then/else
%       parts, conditional and/or etc.

share(X, Z) :- insert_eval(X, Y), trim_eval(Y, Z).

insert_eval(V,                    V) :- var(V), !, V = eval(_, _).
insert_eval(eval(X, Y),  eval(X, Y)) :- !, Y = (_, $).
insert_eval([X | Xs],      [Y | Ys]) :- !, insert_eval(X, Y), insert_eval(Xs, Ys).
insert_eval(A -> B,          A -> Y) :- !, insert_eval(B, Y).
insert_eval(A,                    A) :- atomic(A), !.
insert_eval(FXs,                FYs) :- functor(FXs, F, N), functor(FYs, F, N), FXs =.. [F | Xs], FYs =.. [F | Ys], insert_eval(Xs, Ys).

trim_eval(V,                   V) :- var(V), !.
trim_eval(eval(X, Y),          X) :- Y = (_, Z), var(Z), !.
trim_eval(eval(X, Y), eval(X, Z)) :- !, Y = (Z, _).
trim_eval([X | Xs],     [Y | Ys]) :- !, trim_eval(X, Y), trim_eval(Xs, Ys).
trim_eval(A -> B,         X -> Y) :- !, delete_eval(A, X), trim_eval(B, Y).
trim_eval(A,                   A) :- atomic(A), !.
trim_eval(FXs,               FYs) :- functor(FXs, F, N), functor(FYs, F, N), FXs =.. [F | Xs], FYs =.. [F | Ys], trim_eval(Xs, Ys).

delete_eval(V,                 V) :- var(V), !.
delete_eval(eval(X, _),        X) :- !.
delete_eval([X | Xs],   [Y | Ys]) :- !, delete_eval(X, Y), delete_eval(Xs, Ys).
delete_eval(A,                 A) :- atomic(A), !.
delete_eval(FXs,             FYs) :- functor(FXs, F, N), functor(FYs, F, N), FXs =.. [F | Xs], FYs =.. [F | Ys], delete_eval(Xs, Ys).

%       goal/3 may be handy to integrate Prolog in Husky

goal(G, Env, (X, Y)) :- goal(G, Env, X, Y).

goal(V,       _Env, true,          V) :- var(V), !.
goal([X | Xs], Env, C,      [Y | Ys]) :- !, goal(X, Env, A, Y), !, goal(Xs, Env, B, Ys), conjunction(A, B, C).
goal([],      _Env, true,         []) :- !.
goal(A,        Env, show(X, Y),    Y) :- atom(A), memberchk(A = X, Env), var(X), !.
goal(A,        Env, true,          X) :- atom(A), memberchk(A = {X}, Env), !.
goal(A,       _Env, true,          A) :- atomic(A), !.
goal(FAs,      Env, C,           FBs) :- FAs =.. [F | As], !, goal(As, Env, C, Bs), FBs =.. [F | Bs].

conjunction(true, C,      C) :- !.
conjunction(C, true,      C) :- !.
conjunction(A, B,    (A, B)).

%       constant(+Const)
%       Succeeds when Const is a constant.

constant(A) :- number(A), !.
constant(A) :- string(A), !.
constant(num) :- !.
constant(bool) :- !.
constant(string) :- !.
constant(type) :- !.
constant(true) :- !.
constant(false) :- !.
constant(nil) :- !.
constant('$'(_)) :- !, fail.
constant(A) :-
        atom(A),
        recorded(A, mode(T, M), Ref),
        (       (M = const)
        ->      true
        ;       (M == def)
        ->      fail
        ;       erase(Ref),     % was accepted as type, so should be const
                recorda(A, mode(T, const))
        ).

%       free_var/0
%       Issue error message when a free variable is encountered

free_var :-
        format('Expression contains one or more free variables~n'),
        throw(compile_error).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%       Lazy eval (NOR with sharing and lazy list constructor)

eval($,                             _) :- !, fail.
eval(eval(A -> B, V), eval(A -> B, V)) :- !.
eval(eval(A ; B,  V), eval(A ; B,  V)) :- !.
eval(eval(X,      V),               Y) :- var(V), !, eval(X, Y), (Y = (_ -> _); Y = (_ ; _); V = Y), !. % ensures expressions that produce lambda abstractions are re-evaluated (disables sharing in certain cases of functions as args)
eval(eval(_,      V),               V) :- !.
eval([X | Xs],               [V | Xs]) :- !, eval(X, V).
eval([],                           []) :- !.
eval((X, Y),                   (U, V)) :- !, eval(X, U), eval(Y, V).
eval(A -> B,                   A -> B) :- !.
eval(A ; B,                     A ; B) :- !.
eval(F : A,                         V) :- apply(F, A, X), !, eval(X, V).
eval(F : A,                         V) :- !, eval(F, G), (apply(G, A, X) -> eval(X, V); V = G : A).
eval(A,                             V) :- atom(A), A := X, !, eval(X, V).
eval(X,                             X).

%       Eager eval (AOR)

eaval($,                             _) :- !, fail.
eaval(eval(A -> B, V), eval(A -> B, V)) :- !.
eaval(eval(A ; B,  V), eval(A ; B,  V)) :- !.
eaval(eval(X,      V),               Y) :- var(V), !, eaval(X, Y), (Y = (_ -> _); Y = (_ ; _); V = Y), !. % ensures expressions that produce lambda abstractions are re-evaluated (disables sharing in certain cases of functions as args)
eaval(eval(_,      V),               V) :- !.
eaval([X | Xs],               [V | Vs]) :- !, eaval(X, V), eaval(Xs, Vs).
eaval([],                           []) :- !.
eaval((X, Y),                   (U, V)) :- eaval(X, U), eaval(Y, V).
eaval(A -> B,                   A -> B) :- !.
eaval(A ; B,                     A ; B) :- !.
eaval(F : A,                         V) :- apply(F, A, X), !, eaval(X, V).
eaval(F : A,                         V) :- !, eaval(F, G), (apply(G, A, X) -> eaval(X, V); V = G : A).
eaval(A,                             V) :- atom(A), A := X, !, eaval(X, V).
eaval(X,                             X).

%       lambdas(+Lambdas, ?Lambda)
%       Apply lambda abstraction to argument where Lambdas has alternatives

lambdas(X ; _, X) :- !.
lambdas(_ ; L, X) :- !, lambdas(L, X).
lambdas(X,     X).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%       Built-in operators and delta reductions (graph-rewrite rules)

:- dynamic macro/2.

:- dynamic (:=)/2.
% :- index(1 := 0).

read := S :- current_input(I), read_line_to_codes(I, L), !, string_to_list(S, L).
getc := N :- get_single_char(N), !.

:- dynamic apply/3.
% :- index(apply(1, 0, 0)).

apply(eval(A -> B, _), X,             Z) :- copy_term(A -> B, Y -> Z), !, (var(Y) -> Y = X; eval(X, V) -> Y = V).
apply(     A -> B,     X,             B) :- !, (var(A) -> A = X; eval(X, V) -> A = V).

apply(eval(A ; B, _),  X,             Z) :- eval(X, Y), copy_term(A ; B, L), !, lambdas(L, Y -> Z).
apply(     A ; B,      X,             Z) :- eval(X, Y), !, lambdas(A ; B, Y -> Z).

apply(hd,              X,             H) :- eval(X, Y), Y = [H | _], !.
apply(hd,              _,           nil) :- !.

apply(tl,              X,             T) :- eval(X, Y), Y = [_ | T], !.
apply(tl,              _,           nil) :- !.

apply(fix,             F, eval(F, _) : (fix : F)) :- !. % do not create cyclic graph
%apply(fix,             F,          FixF) :- !, FixF = (eval(F, _):FixF).       % create cyclic graph: can be problematic for some Prologs

apply((\),             X,          true) :- eval(X, X1), X1 == false, !.
apply((\),             _,         false) :- !.

apply(id,              X,             X) :- !.

apply(neg,             X,             V) :- !, eval(X, N), V is -N.

apply(abs,             X,             V) :- !, eval(X, N), V is abs(N).

apply(sin,             X,             V) :- !, eval(X, N), V is sin(N).

apply(cos,             X,             V) :- !, eval(X, N), V is cos(N).

apply(tan,             X,             V) :- !, eval(X, N), V is tan(N).

apply(asin,            X,             V) :- !, eval(X, N), V is asin(N).

apply(acos,            X,             V) :- !, eval(X, N), V is acos(N).

apply(atan,            X,             V) :- !, eval(X, N), V is atan(N).

apply(log,             X,             V) :- eval(X, N), N >= 0, !, V is log(N).
apply(log,             _,           nil) :- !.

apply(exp,             X,             V) :- !, eval(X, N), V is exp(N).

apply(sqrt,            X,             V) :- eval(X, N), N >= 0, !, V is sqrt(N).
apply(sqrt,            _,           nil) :- !.

apply(num,             X,             N) :- eval(X, S), atom_number(S, N), !.
apply(num,             _,           nil) :- !.

apply(str,             X,             S) :- eval(X, N), number(N), !, string_to_atom(S, N).

apply(s2ascii,         X,             L) :- !, eval(X, S), string_to_list(S, L).

apply(ascii2s,         X,             S) :- !, eval(X, L), show(L, L1), string_to_list(S, L1).

apply(write,           X,             V) :- !, eval(X, V), (string(V) -> write(V); show(V)).

apply(writeln,         X,             V) :- !, eval(X, V), (string(V) -> writeln(V); show(V), nl).

apply(putc,            X,             V) :- !, eval(X, V), put_char(V).

apply((load),          F,          true) :-
        eval(F, S),
        absolute_file_name(S, [access(read), extensions(['sky', '']), file_errors(fail)], A),
        flag(profiling, _, 0),
        see(A),
        repeat, read_term(T, [module(husky), variable_names(Bindings)]),
                husky(T, Bindings),
        T == end_of_file, !,
        seen.
apply((load),          _,         false) :- !.

apply((save),          F,          true) :-
        eval(F, S),
        absolute_file_name(S, [access(write), extensions(['sky', '']), file_errors(fail)], A),
        flag(profiling, _, 0),
        tell(A), !,
        pragma(listing),
        told.
apply((save),          _,         false) :- !.

apply(F: X,            Y,             Z) :- apply(F, X, Y, Z).

% :- index(apply(1, 0, 0, 0)).

apply((:), F,          X,          F: X) :- !.

apply(',', X,          Y,        (X, Y)) :- !.

apply((.), X,          Y,       [X | Y]) :- !.

apply((+), X,          Y,             Z) :- !, eval(X, N), eval(Y, M), Z is (N + M).

apply((-), X,          Y,             Z) :- !, eval(X, N), eval(Y, M), Z is (N - M).

apply((*), X,          Y,             Z) :- !, eval(X, N), eval(Y, M), Z is (N * M).

apply((/), X,          Y,             Z) :- !, eval(X, N), eval(Y, M), M \== 0, !, Z is (N / M).

apply((rdiv), X,       Y,             Z) :- !, eval(X, N), eval(Y, M), M \== 0, !, Z is (N rdiv M).

apply((div), X,        Y,             Z) :- !, eval(X, N), eval(Y, M), M \== 0, !, Z is (N // M).

apply((mod), X,        Y,             Z) :- !, eval(X, N), eval(Y, M), M \== 0, !, Z is (N mod M).

apply((^), X,          Y,             Z) :- !, eval(X, N), eval(Y, M), Z is N ^ M.

apply((min), X,        Y,             Z) :- !, show(X, X1), show(Y, Y1), ( X1 =< Y1, Z = X1; Z = Y1).

apply((max), X,        Y,             Z) :- !, show(X, X1), show(Y, Y1), ( X1 >= Y1, Z = X1; Z = Y1).

apply((=), X,          Y,             F) :- !, show(X, X1), show(Y, Y1), (X1 =@= Y1 -> F = true; F = false).

apply((<>), X,         Y,             F) :- !, show(X, X1), show(Y, Y1), (X1 =@= Y1 -> F = false; F = true).

apply((<), X,          Y,             F) :- !, show(X, X1), show(Y, Y1), (X1 @< Y1 -> F = true; F = false).

apply((>), X,          Y,             F) :- !, show(X, X1), show(Y, Y1), (X1 @> Y1 -> F = true; F = false).

apply((<=), X,         Y,             F) :- !, show(X, X1), show(Y, Y1), (X1 @=< Y1 -> F = true; F = false).

apply((>=), X,         Y,             F) :- !, show(X, X1), show(Y, Y1), (X1 @>= Y1 -> F = true; F = false).

apply((/\), X,         Y,             Z) :- !, eval(X, X1), ((X1 == true) -> eval(Y, Z); Z = false).

apply((\/), X,         Y,             Z) :- !, eval(X, X1), ((X1 == false) -> eval(Y, Z); Z = true).

apply((//), X,         Y,             S) :- !, eval(X, X1), eval(Y, Y1), string_concat(X1, Y1, S).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%       type(+Expr, -Type)
%       Type check/infer Expr
%       As is commonly known, type checking on recursive functions may fail in
%       some cases to find the exact type because the function in the function
%       body has a variable type that is not instantiated at the end of the
%       inference. Here, the instantiation takes not place because the
%       function's type is recorded as a side effect.

type(Expr, Type) :-
        copy_term(Expr, Term),
        catch(Term :: Type, type_error, true).
type(Expr, _Type) :-
        decompile(Expr, Term),
        format('Type error in ~p~n', [Term]),
        fail.

%       Types of built-in operators

(_ :: Alpha) :: Alpha :- !.     % the type of a variable is a variable type

(load) :: string -> bool :- !.
(save) :: string -> bool :- !.

(A -> B) :: Alpha -> Beta :- A :: Alpha, B :: Beta.

(A; B) :: Alpha :- A :: Alpha, B :: Beta, unify_with_occurs_check(Alpha, Beta).

F:A :: Beta :- !, A :: Alpha, F :: Gamma, unify_with_occurs_check(Gamma, (Alpha -> Beta)).

[X | Xs] :: [Alpha] :- !, X :: Alpha, !, Xs :: [Beta], unify_with_occurs_check(Alpha, Beta).
[]       :: [_] :- !.

(X,Y) :: (Alpha, Beta) :- !, X :: Alpha, !, Y :: Beta.

(:) :: (Alpha -> Beta) -> Alpha -> Beta :- !.
(.) :: Alpha -> [Alpha] -> [Alpha] :- !.
',' :: Alpha -> Beta -> (Alpha, Beta) :- !.

fix :: (Alpha -> Alpha) -> Alpha :- !.

(+)    :: num -> num -> num :- !.
(-)    :: num -> num -> num :- !.
(*)    :: num -> num -> num :- !.
(/)    :: num -> num -> num :- !.
(rdiv) :: num -> num -> num :- !.       % SWI-Prolog rational division
(div)  :: num -> num -> num :- !.
(mod)  :: num -> num -> num :- !.
(^)    :: num -> num -> num :- !.
(/\)   :: bool -> bool -> bool :- !.
(\/)   :: bool -> bool -> bool :- !.
(\)    :: bool -> bool :- !.
id     :: Alpha -> Alpha :- !.
neg    :: num -> num :- !.
abs    :: num -> num :- !.
sin    :: num -> num :- !.
cos    :: num -> num :- !.
tan    :: num -> num :- !.
asin   :: num -> num :- !.
acos   :: num -> num :- !.
atan   :: num -> num :- !.
log    :: num -> num :- !.
exp    :: num -> num :- !.
sqrt   :: num -> num :- !.
(=)    :: Alpha -> Alpha -> bool :- !.
(<>)   :: Alpha -> Alpha -> bool :- !.
(<)    :: Alpha -> Alpha -> bool :- !.
(>)    :: Alpha -> Alpha -> bool :- !.
(<=)   :: Alpha -> Alpha -> bool :- !.
(>=)   :: Alpha -> Alpha -> bool :- !.
(min)  :: num -> num -> num :- !.
(max)  :: num -> num -> num :- !.

hd :: [Alpha] -> Alpha :- !.
tl :: [Alpha] -> [Alpha] :- !.

num :: string -> num :- !.

str :: num -> string :- !.

s2ascii :: string -> [num] :- !.

ascii2s :: [num] -> string :- !.

read :: string :- !.

write :: Alpha -> Alpha :- !.
writeln :: Alpha -> Alpha :- !.

getc :: num :- !.

putc :: num -> num :- !.

nil :: _ :- !.

true  :: bool :- !.
false :: bool :- !.

(//) :: string -> string -> string :- !.

N :: num    :- number(N), !.
S :: string :- string(S), !.

X :: T :- recorded(X, mode(T, _)), !.

X :: T :- nonvar(T), !, decompile(T, T1), format('~p is not of type ~p~n', [X, T1]), throw(type_error).
X :: _ :- atom(X), format('Undeclared symbol ~p~n', [X]), throw(type_error).
X :: _ :- decompile(X, Y), format('Cannot infer type of ~p~n', [Y]), throw(type_error).
