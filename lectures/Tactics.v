(** * Тактики: Больше тактик богу тактик! *)

Set Warnings "-notation-overridden".
From Lectures Require Export Poly.

(* ################################################################# *)
(** * Тактика [apply] *)

(** Тактика [apply] полезна, когда какая-то из гипотез либо ранее
    объявленная лемма в точности совпадает с целью: *)

Theorem silly1 : forall (n m : nat),
  n = m ->
  n = m.
Proof.
  intros n m eq.

(** Здесь можно завершить с "[rewrite -> eq.  reflexivity.]", как мы делали
    раньше. Либо можно завершить в один шаг с помощью [apply]: *)

  apply eq.  Qed.

(** [apply] также работает с _обусловленными_ гипотезами: *)

Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.  Qed.

(** Обратите внимание, как Rocq выбирает подходящие значения
    для переменных, захваченных в гипотезе квантором [forall]: *)

Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m)  ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.  Qed.

(** Чтобы [apply] сработала, цель и гипотеза должны _полностью_
    совпадать: *)

Theorem silly3 : forall (n m : nat),
  n = m ->
  m = n.
Proof.
  intros n m H.

  (** Здесь нельзя использовать [apply] напрямую... *)

  Fail apply H.

  (** ...но можно сначала применить тактику [symmetry], которая поменяет местами
      левую и правую части равенства в цели. *)

  symmetry. apply H.  Qed.

(* ################################################################# *)
(** * Тактика [apply with] *)

(** Следующий простенький пример использует два переписывания подряд, чтобы
    перейти от [[a;b]] к [[e;f]]. *)

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. apply eq2. Qed.

(** Так как это частый паттерн, давайте его вынесем в качестве леммы, которая
    раз и навсегда устанавливает, что равенство транзитивно. *)

Theorem trans_eq : forall (X:Type) (x y z : X),
  x = y -> y = z -> x = z.
Proof.
  intros X x y z eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity.  Qed.

(** Применение этой леммы к примеру выше требует небольшого изменения
    при применении [apply]: *)

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.

  (** Просто [apply trans_eq] не сработает!  А вот... *)
  apply trans_eq with (y:=[c;d]).
  (** поможет. *)

  apply eq1. apply eq2.   Qed.

(** [транзитивность] также доступна в качестве тактики. *)

Example trans_eq_example'' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d].
  apply eq1. apply eq2.   Qed.

(* ################################################################# *)
(** * Тактики [injection] и [discriminate] *)

(** Конструкторы индуктивных типов _инъективны_ и _различны_.

    Например, для [nat]...

       - Если [S n = S m], то обязательно верно, что [n = m]

       - [O] не равно [S n] ни для какого [n]
 *)

(** Мы можем _доказать_ инъективность [S] с помощью функции [pred], определённой
    в [Basics.v]. *)

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2. rewrite H1. simpl. reflexivity.
Qed.

(** Для удобства, тактика [injection] позволяет нам пользоваться
    инъективностью любого конструктора (не только [S]). *)

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H as Hnm. apply Hnm.
Qed.

(** А вот более интересный пример, который показывает, как [injection] можно
    использовать, чтобы получить сразу несколько новых равенств. *)

Theorem injection_ex1 : forall (n m o : nat),
  [n;m] = [o;o] ->
  n = m.
Proof.
  intros n m o H.
  (* РАЗБИРАЕМ НА ЛЕКЦИИ *) Admitted.

(** Про инъективность понятно.  Что насчёт отсутствия пересечений? *)

(** Два терма, начинающиеся с применения различных конструкторов (как то
    [O] и [S] либо [true] и [false]) никогда не равны друг другу! *)

(** Тактика [discriminate] воплощает этот принцип: она применяется к гипотезе,
    содержащей равенство между различными конструкторами (например,
    [false = true]), и немедленно выполняет текущую цель.  Парочка примеров: *)

Theorem discriminate_ex1 : forall (n m : nat),
  false = true ->
  n = m.
Proof.
  intros n m contra. discriminate contra. Qed.

Theorem discriminate_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. Qed.

(** Эти примеры -- конкретные проявления логического принципа, известного как
    _принцип взрыва_, который утверждает, что из противоречивого утверждения
    следует что угодно (даже очевидно ложные вещи!). *)

(** В качестве более полезного примера, рассмотрим применение [discriminate]
    для установления связи между двумя различными видами равенства ([=] и [=?]),
    которые мы определяли для натуральных чисел. *)
Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n.

  destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    intros H. reflexivity.

  - (* n = S n' *)
    simpl.

    intros H. discriminate H.
Qed.


(* QUIZ

    Вспомним типы [rgb] и [color]:

Inductive rgb : Type :=  red | green | blue.
Inductive color : Type :=  black | white | primary (p: rgb).

Предположим, состояние доказательства на Rocq выглядит как

         x : rgb
         y : rgb
         H : primary x = primary y
         ============================
          y = x

    и мы применяем тактику [injection H as Hxy].  Что произойдёт?

    (1) "No more subgoals."

    (2) Тактика не применится и вызовет исключение.

    (3) Гипотеза [H] превратится в [Hxy : x = y].

    (4) Ничего из вышеперечисленного.
*)
(* QUIZ

    Положим, состояние доказательства на Rocq выглядит как

         x : bool
         y : bool
         H : negb x = negb y
         ============================
          y = x

    и мы применяем тактику [injection H as Hxy].  Что произойдёт?

    (A) "No more subgoals."

    (B) Тактика не применится и вызовет исключение.

    (C) Гипотеза [H] превратится в [Hxy : x = y].

    (D) Ничего из вышеперечисленного.
*)
(* QUIZ

    Теперь положим, что состояние доказательства на Rocq выглядит как

         x : nat
         y : nat
         H : x + 1 = y + 1
         ============================
          y = x

    и мы применяем тактику [injection H as Hxy].  Что произойдёт?

    (A) "No more subgoals."

    (B) Тактика не применится и вызовет исключение.

    (C) Гипотеза [H] превратится в [Hxy : x = y].

    (D) Ничего из вышеперечисленного.
*)
(* QUIZ

    Наконец, положим, что состояние доказательства на Rocq выглядит как

         x : nat
         y : nat
         H : 1 + x = 1 + y
         ============================
          y = x

    и мы применяем тактику [injection H as Hxy].  Что произойдёт?

    (A) "No more subgoals."

    (B) Тактика не применится и вызовет исключение.

    (C) Гипотеза [H] превратится в [Hxy : x = y].

    (D) Ничего из вышеперечисленного.
*)

(** Инъективность конструкторов позволяет нам установить, что
    [forall (n m : nat), S n = S m -> n = m].  Обратное утверждение -- частный
    случай более общего факта, верного как для конструкторов, так и для функций.
    Он нам очень пригодится дальше: *)

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq.  reflexivity.  Qed.

Theorem eq_implies_succ_equal : forall (n m : nat),
  n = m -> S n = S m.
Proof. intros n m H. apply f_equal. apply H. Qed.

(** Rocq также предоставляет [f_equal] в виде тактики. *)

Theorem eq_implies_succ_equal' : forall (n m : nat),
  n = m -> S n = S m.
Proof. intros n m H. f_equal. apply H. Qed.

(* ################################################################# *)
(** * Применение тактик к гипотезам *)

(** У многих тактик доступна вариация вида "[... in ...]", которая
    вместо цели применяется к гипотезе. *)

Theorem S_inj : forall (n m : nat) (b : bool),
  ((S n) =? (S m)) = b  ->
  (n =? m) = b.
Proof.
  intros n m b H. simpl in H. apply H.  Qed.

(** Обычный способ применения тактики [apply] -- это так называемый
    "обратный ход рассуждений."  По сути, пользуясь им, мы говорим "Мы пытаемся
    доказать [X] и мы знаем [Y -> X], так что нам достаточно доказать [Y]."

    А вот вариация [apply... in...] -- это, наоборот, "прямой ход рассуждений":
    он говорит "Мы знаем, что [Y] и что [Y -> X], так что мы знаем [X]." *)

Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n ->
  q = p.
Proof.
  intros n m p q EQ H.
  symmetry in H. apply EQ in H. symmetry in H.
  apply H.  Qed.

(* ################################################################# *)
(** * Уточнение гипотезы *)

(** Другая полезная для работы с гипотезами тактика называется [specialize].
    По сути, это комбинация [assert] и [apply], но она достаточно часто
    предоставляет до приятного аккуратный способ уточнить слишком общие
    предположения.  Она работает следующим образом:

    Если [H] в текущем контексте это гипотеза с квантором, т.е. имеющая вид
    [H : forall (x:T), P], тогда [specialize H with (x := e)] изменит [H] так,
    что она теперь будет иметь тип [[x:=e]P], т.е., [P], где [x] заменили на
    [e].

    Например: *)

Theorem specialize_example: forall n,
     (forall m, m*n = 0)
  -> n = 0.
Proof.
  intros n H.
  specialize H with (m := 1).
  rewrite mult_1_l in H.
  apply H. Qed.

(** Используя [specialize] до [apply], мы можем дополнительно проконтролировать,
    где и какую работу выполняет тактика [apply]. *)
Example trans_eq_example''' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  specialize trans_eq with (y:=[c;d]) as H.
  apply H.
  apply eq1.
  apply eq2. Qed.
(** Заметим:
    - Мы можем [уточнять] факты и из глобального контекста, не только локальные
      предположения.
    - Клоза [as...] в конце сообщает [specialize], как в таком случае называть
      новую гипотезу. *)

(* ################################################################# *)
(** * Варьирование предположения индукции *)

(** Вспомним функцию для удвоения натурального числа из главы [Induction]:
    *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** Пусть мы хотим показать, что [double] инъективна (т.е. разные
    аргументы отображаются в разные значения).  _Начинаем_ это доказательство мы
    очень осторожно: *)

Theorem double_injective_FAILED : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) discriminate eq.
    + (* m = S m' *) f_equal.

(** Здесь предположение индукции ([IHn']) _не_ утверждает [n' = m'] --
    мешается лишняя [S] -- так что цель нам, увы, не доказать. *)

Abort.
(** Что пошло не так? *)

(** Попытка доказать утверждение индукцией по [n], когда [m] уже в контексте,
    не работает, потому что так мы пытаемся доказать утверждение для
    _произвольного_ [n], но лишь для некоторого _конкретного_ [m]. *)

(** Успешное доказательство [double_injective] оставляет [m] под квантором
    вплоть до того момента, когда мы вызываем [индукцию] по [n]: *)

Theorem double_injective : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *)
    intros m eq.
    destruct m as [| m'] eqn:E.
    + (* m = O *)
    discriminate eq.
    + (* m = S m' *)
      f_equal.
      apply IHn'. simpl in eq. injection eq as goal. apply goal. Qed.

(** Урок, который нужно из этого вынести, следующий: при использовании индукции
    нужно аккуратно следить за тем, чтобы не доказывать излишне конкретное
    утверждение. Так, когда вы доказываете утверждение про переменные [n] и [m]
    индукцией по [n], иногда принципиально важно, чтобы [m] оставалась под
    квантором.

    Следующая теорема, усиливающая связь между [=?] и [=], следует этому
    же принципу. *)
Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
  (* РАЗБИРАЕМ НА ЛЕКЦИИ *) Admitted.

(** Стратегия делать меньше [intros] перед [induction] для получения более
    сильного предположения индукции работает не всегда; иногда переменные
    под кванторами нужно _поменять местами_.  Предположим, например, что мы
    хотим доказать [double_injective] индукцией не по [n], а по [m]. *)

Theorem double_injective_take2_FAILED : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m. induction m as [| m' IHm'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) f_equal.
        (* Здесь мы застряли точно так же, как раньше. *)
Abort.

(** Проблема в том, что, для использования [m], мы должны сначала ввести [n].
    (А если мы скажем [induction m], ничего не вводя, Rocq автоматически введёт
    [n] за нас!) *)

(** Вместо этого мы можем сначала ввести все подкванторные переменные, а
    затем _заново обобщить утверждение_ по некоторым из них.  Тактика
    [generalize dependent] делает именно это. *)

Theorem double_injective_take2 : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m.
  (* И [n], и [m] уже в контексте. *)
  generalize dependent n.
  (* Теперь [n] снова вводится в цели, так что мы можем запустить индукцию
     по [m] и получить достаточно общую индукционную гипотезу. *)
  induction m as [| m' IHm'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) f_equal.
      apply IHm'. injection eq as goal. apply goal. Qed.

(* ################################################################# *)
(** * Переписывание и предположения с условиями *)

(** Пусть мы хотим показать, что [plus] обратный к [minus].  Раз мы работаем
    с натуральными числами, нам нужно дополнительное предположение, чтобы
    [minus] не обрезал результат. Так, предположение индукции будет выглядеть
    как [forall m, n' <=? m = true -> (m - n') + n' = m].  Начало доказательства
    использует техники, которые мы уже видели -- в частности, обратите внимание,
    как мы запускаем индукцию по [n] перед введением [m], так что предположение
    индукции становится достаточно общим. *)

Lemma sub_add_leb : forall n m, n <=? m = true -> (m - n) + n = m.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - (* n = 0 *)
    intros m H. rewrite add_0_r. destruct m as [| m'].
    + (* m = 0 *)
      reflexivity.
    + (* m = S m' *)
      reflexivity.
  - (* n = S n' *)
    intros m H. destruct m as [| m'].
    + (* m = 0 *)
      discriminate.
    + (* m = S m' *)
      simpl in H. simpl. rewrite <- plus_n_Sm.

    (** Мы могли бы использовать тактику [assert], чтобы вывести
    [(m' - n') + n' = m'] из предположения индукции; оказывается, вместо этого
    мы можем сразу использовать [rewrite]... *)

      rewrite IHn'.
      * reflexivity.
      * apply H.
Qed.

(* ################################################################# *)
(** * Раскрытие утверждений *)

(** Иногда случается так, что нам нужно вручную подставить определение вместо
    имени, введённого с помощью [Definition], чтобы мы могли работать
    с выражением, которое оно обозначает.

    Например, если мы определим... *)

Definition square n := n * n.

(** ...и попытаемся доказать простой факт о [square]... *)

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.

(** ...то мы как будто бы застрянем: [simpl] ничего не упрощает, и раз мы
    не доказали никаких других фактов о [square], то нам нечего использовать
    с [apply] и [rewrite]. *)

(** Чтобы продвинуться, мы можем вручную [раскрыть] ([unfold]) определение
    [square]: *)

  unfold square.

(** Теперь нам есть с чем работать: обе части равенства -- это выражения,
    использующие умножение, а у нас накопилось достаточно фактов об умножении.
    В частности, мы знаем, что оно коммутативно и ассоциативно, так что, исходя
    из этого, доказательство закончить несложно. *)

  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
    { rewrite mul_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.

(** В этом месте пора поговорить про раскрытие и упрощения чуть глубже.

    Мы уже видели, что тактики вроде [simpl], [reflexivity] и [apply] часто
    раскрывают определения функций автоматически, если это позволяет им
    продвинуться.  Например, если мы положим [foo m] константой [5]... *)

Definition foo (x: nat) := 5.

(** .... то [simpl] в следующем доказательстве (или [reflexivity], если мы
    опустим [simpl]) раскроет [foo m] в [(fun x => 5) m] и далее упростит это
    выражение до [5]. *)

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

(** Однако такое автоматическое раскрытие достаточно консервативно.  Например,
    если мы определим чуть более сложную функцию с помощью сопоставления
    с образцом... *)

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

(** ...то аналогичное доказательство застрянет: *)

Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl. (* Ничего не делает! *)
Abort.

(** Теперь есть два способа продвинуться.

    Во-первых, мы можем использовать [destruct m], чтобы разбить доказательство
    на два случая: *)

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(** Этот подход сработает, но он опирается на наше знание о внутреннем
    устройстве [bar], содержащей [match] внутри, который мешает нам
    продвинуться. *)

(** Сперва мы можем попросить Rocq раскрыть определение [bar]. *)

Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.

(** Теперь мы ясно видим, что застряли на [match] с обеих сторон [=], и можем
    использовать [destruct], чтобы закончить доказательство, особо не мучаясь
    с выбором. *)

  destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

(* ################################################################# *)
(** * Применение [destruct] к составным выражениям *)

(** Тактику [destruct] можно применять не только к переменным, но и
    к произвольным выражениям: *)

Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
    - (* n =? 3 = true *) reflexivity.
    - (* n =? 3 = false *) destruct (n =? 5) eqn:E2.
      + (* n =? 5 = true *) reflexivity.
      + (* n =? 5 = false *) reflexivity.  Qed.

(** Часть [eqn:] тактики [destruct] необязательная; хоть мы и придерживаемся
    того, чтобы её выписывать ради улучшения документируемости, её зачастую
    можно совершенно спокойно опустить.

    Один из случаев, когда её опустить _нельзя_ -- когда мы разбираем случаи
    сложного выражения; в данном случае информация, заложенная в [eqn:], может
    оказаться критически важной для доказательства и, если мы её опустим, то
    [destruct] может стереть информацию, необходимую для доказательства. *)

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

Theorem sillyfun1_odd_FAILED : forall (n : nat),
  sillyfun1 n = true ->
  odd n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3).
  (* застряли... *)
Abort.

(** Квалификатор [eqn:] сохраняет эту информацию так, чтобы мы смогли её
    использовать. *)

Theorem sillyfun1_odd : forall (n : nat),
  sillyfun1 n = true ->
  odd n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:Heqe3.
    - (* e3 = true *) apply eqb_true in Heqe3.
      rewrite -> Heqe3. reflexivity.
    - (* e3 = false *)
      destruct (n =? 5) eqn:Heqe5.
        + (* e5 = true *)
          apply eqb_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        + (* e5 = false *) discriminate eq.  Qed.

(* ################################################################# *)
(** * Микро-поучение *)

(** Бездумный подбор доказательств ужасно искушает...

    Постарайтесь устоять!
*)


