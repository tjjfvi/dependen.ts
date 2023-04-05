const Nat = def(Type, Fn(Type, T => Fn(Fn(T, _ => T), () => Fn(T, _ => T))))

const zero = def(Nat, fn(Type, T => fn(Fn(T, _ => T), () => fn(T, x => x))))
const succ = def(
  Fn(Nat, _ => Nat),
  fn(
    Nat,
    n =>
      fn(
        Type,
        T => fn(Fn(T, _ => T), f => fn(T, x => call(call(call(n, T), f), call(f, x)))),
      ),
  ),
)

const add = def(
  Fn(Nat, _ => Fn(Nat, _ => Nat)),
  fn(
    Nat,
    a =>
      fn(Nat, b =>
        fn(Type, T =>
          fn(
            Fn(T, _ => T),
            f => fn(T, x => call(call(call(a, T), f), call(call(call(b, T), f), x))),
          ))),
  ),
)

const one = def(Nat, call(succ, zero))
const two = def(Nat, call(succ, one))

const four = def(call(call(add, two), two))
//    ^?

// --- //

type _ = {}

type N = _[]
type Inc<T extends N> = [...T, _]

type Term<T extends $, D extends N> = {
  new(depth: D): T
}

interface InputTerm<T extends $, D extends N> {
  new(depth: D): T
}

interface OutputTerm<T extends $, D extends N = []> {
  new<E extends N>(depth: E): Raise<T, E, D>
}

type NoInfer<T> = T extends infer U ? U : never

declare function call<T extends $, U extends $, D extends N>(
  fn: InputTerm<T & { __type: { kind: "pi" } }, NoInfer<D>>,
  arg: InputTerm<U & { __type: T["__type"] extends Pi<infer P, infer R> ? P : never }, NoInfer<D>>,
): Term<Reduce<App<T, U>>, D>

declare function fn<P extends $, R extends $, D extends N = []>(
  par: InputTerm<P, NoInfer<D>>,
  fn: (x: OutputTerm<Var<[], Alpha<P>>, Inc<D>>) => InputTerm<R, Inc<D>>,
): Term<Lam<P, R>, D>

declare function Fn<P extends $, R extends $, D extends N = []>(
  par: InputTerm<P, NoInfer<D>>,
  fn: (x: OutputTerm<Var<[], Alpha<P>>, Inc<D>>) => InputTerm<R, Inc<D>>,
): Term<Pi<P, R>, D>

type Raise<T extends $, D extends N, E extends N = []> = D extends [_, ...E, ...infer F extends N]
  ? Raise<Alpha<T>, [...E, ...F], E>
  : T

declare function def<T extends $, V extends $>(
  ty: InputTerm<T, []>,
  t: InputTerm<V & { __type: T }, []>,
): OutputTerm<V>
declare function def<V extends $>(
  t: InputTerm<V, []>,
): OutputTerm<V>

declare const Type: Term<Type, any>

type $ = { kind: "type" | "pi" | "lam" | "app" | "var" | symbol; __type: $ }

interface Type {
  kind: "type"
  __type: Type
}

interface Pi<P extends $, R extends $> {
  kind: "pi"
  par: P
  ret: R
  __type: Type
}

interface Lam<P extends $, R extends $> {
  kind: "lam"
  par: P
  ret: R
  __type: Pi<P, R["__type"]>
}

interface App<F extends $, A extends $> extends $ {
  kind: "app"
  fun: F
  arg: A
  __type: Replace<F["__type"] extends Pi<infer P, infer R> ? R : never, [], A>
}

interface Var<D extends N, T extends $> {
  kind: "var"
  depth: D
  __type: T
}

type DecAbove<A extends N, B extends N> = A extends [_, ...B, ...infer C extends N] ? [...B, ...C]
  : A

type IncAbove<A extends N, B extends N> = A extends [...B, ...infer C extends N] ? [...B, ...C, _]
  : A

type Replace<X extends $, D extends N, A extends $> = X extends Var<infer E, infer T>
  ? E extends D ? A : Var<DecAbove<E, D>, Replace<T, D, A>>
  : X extends Pi<infer P, infer R> ? Pi<Replace<P, D, A>, Replace<R, Inc<D>, Alpha<A, D>>>
  : X extends Lam<infer P, infer R> ? Lam<Replace<P, D, A>, Replace<R, Inc<D>, Alpha<A, D>>>
  : X extends App<infer P, infer R> ? App<Replace<P, D, A>, Replace<R, D, A>>
  : X

type Alpha<X extends $, D extends N = []> = X extends Var<infer E, infer T>
  ? Var<IncAbove<E, D>, Alpha<T, D>>
  : X extends Pi<infer P, infer R> ? Pi<Alpha<P, D>, Alpha<R, Inc<D>>>
  : X extends Lam<infer P, infer R> ? Lam<Alpha<P, D>, Alpha<R, Inc<D>>>
  : X extends App<infer F, infer A> ? App<Alpha<F, D>, Alpha<A, D>>
  : X

type Reduce<X extends $> = X extends Var<infer D, infer T> ? Var<D, T>
  : X extends Pi<infer P, infer R> ? Pi<Reduce<P>, Reduce<R>>
  : X extends Lam<infer P, infer R> ? Lam<Reduce<P>, Reduce<R>>
  : X extends App<infer F, infer A>
    ? Reduce<F> extends infer F extends $
      ? F extends Lam<infer _, infer R> ? Reduce<Replace<R, [], A>> : App<F, Reduce<A>>
    : never
  : X
