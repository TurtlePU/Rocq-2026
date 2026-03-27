(** * Imp: Простые императивные программы *)

(** В этой главе мы обращаем наше внимание на то, как использовать Rocq
    в качестве инструмента для изучения других инструментов.  Нашим учебным
    примером будет _простой императивный язык программирования_ под названием
    Imp, содержащий ключевые элементы конвенциональных мейнстримных языков
    программирования вроде C и Java.

    Вот знакомая Вам математическая функция, записанная на Imp.

       Z := X;
       Y := 1;
       while Z <> 0 do
         Y := Y * Z;
         Z := Z - 1
       end
*)

(** Здесь мы концентрируемся на определении _синтаксиса_ и _семантики_ Imp;
    далее, во втором томе учебника, мы развиваем теорию _эквивалентности
    программ_ и вводим _Логику Хоара_, популярную логику для рассуждения об
    императивных программах. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Bool.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import EqNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Strings.String.
From LF Require Import Maps.

(* ################################################################# *)
(** * Арифметические и логические выражения *)

(** Мы представим Imp в трёх частях: начнём с языка _арифметических и логических
    выражений_, затем расширим его _переменными_, и, наконец, введём язык
    _команд_, включающий присваивания, условные ветвления, последовательное
    исполнение и циклы. *)

(* ================================================================= *)
(** ** Синтаксис *)

Module AExp.

(** _Абстрактные синтаксические деревья_ (AST) для арифметических
    и логических выражений: *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

(* ================================================================= *)
(** ** Вычисление *)

(** _Вычисление_ арифметического выражения в результате получает число. *)

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus  a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult  a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

(** Аналогично, логические выражения вычисляются в значение типа [bool]. *)

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval a1) =? (aeval a2)
  | BNeq a1 a2  => negb ((aeval a1) =? (aeval a2))
  | BLe a1 a2   => (aeval a1) <=? (aeval a2)
  | BGt a1 a2   => negb ((aeval a1) <=? (aeval a2))
  | BNot b1     => negb (beval b1)
  | BAnd b1 b2  => andb (beval b1) (beval b2)
  end.

(* QUIZ

    Во что вычисляется следующее выражение?

  aeval (APlus (ANum 3) (AMinus (ANum 4) (ANum 1)))

  (A) true

  (B) false

  (C) 0

  (D) 3

  (E) 6

*)

(* ================================================================= *)
(** ** Оптимизация *)

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus  e1 e2 => APlus  (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult  e1 e2 => AMult  (optimize_0plus e1) (optimize_0plus e2)
  end.

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - (* ANum *) reflexivity.
  - (* APlus *) destruct a1 eqn:Ea1.
    + (* a1 = ANum n *) destruct n eqn:En.
      * (* n = 0 *)  simpl. apply IHa2.
      * (* n <> 0 *) simpl. rewrite IHa2. reflexivity.
    + (* a1 = APlus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMinus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMult a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - (* AMinus *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - (* AMult *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.  Qed.

(* ################################################################# *)
(** * Автоматизация в Rocq *)

(** Это доказательство было не без самоповторов.  Пора изучить пару новых
    трюков на Rocq... *)

(* ================================================================= *)
(** ** Тактикалы *)

(** _Тактикалы_ -- термин в Rocq для тактик, принимающих другие тактики
    в качестве аргументов; условно говоря, "тактики высшего порядка".  *)

(* ----------------------------------------------------------------- *)
(** *** Тактикал [try] *)

(** Если [T] -- тактика, то [try T] -- тактика, которая ведёт себя почти как
    [T], но, если [T] выбрасывает исключение, то [try T] _успешно_ ничего
    не делает (вместо того, чтобы тоже выбросить исключение). *)
Theorem silly1 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity. (* Просто [reflexivity] выбросило бы исключение. *)
  apply HP. (* Мы всё ещё можем закончить доказательство другим способом. *)
Qed.

Theorem silly2 : forall ae, aeval ae = aeval ae.
Proof.
    try reflexivity. (* А здесь просто срабатывает [reflexivity]. *)
Qed.

(* ----------------------------------------------------------------- *)
(** *** Тактикал [;] (упрощённая форма) *)

(** В своей наиболее частой форме, тактикал [;] принимает две тактики в качестве
    аргументов.  Получающаяся тактика [T;T'] сперва выполняет [T], а затем
    применяет [T'] к _каждой подцели_, сгенерированной [T]. *)

(** Например: *)

Lemma foo : forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n.
    (* Создаёт две подцели, каждая из которых решается идентично...  *)
    - (* n=0 *) simpl. reflexivity.
    - (* n=Sn' *) simpl. reflexivity.
Qed.

(** Мы можем упростить доказательство с помощью тактикала [;]: *)

Lemma foo' : forall n, 0 <=? n = true.
Proof.
  intros.
  (* [destruct] к текущей цели *)
  destruct n;
  (* затем [simpl] к каждой полученной подцели *)
  simpl;
  (* и [reflexivity] в каждой оставшейся подцели *)
  reflexivity.
Qed.

(** Используя [try] и [;] одновременно, мы можем избавиться от тех самоповторов,
    которые нас так беспокоили ещё совсем недавно. *)

Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Большинство случаев сразу следуют из предположения индукции... *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
    (* ... однако оставшиеся -- ANum и APlus -- другие: *)
  - (* ANum *) reflexivity.
  - (* APlus *)
    destruct a1 eqn:Ea1;
      (* Опять же, большинство случаев следуют напрямую из IH: *)
      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).
    (* Интересный случай, в котором [try...] ничего не делает, случается, когда
       [e1 = ANum n]. Здесь нам нужно разобрать случаи по [n] (чтобы понять,
       применяется ли оптимизация) и переписать по предположению индукции. *)
    + (* a1 = ANum n *) destruct n eqn:En;
      simpl; rewrite IHa2; reflexivity.   Qed.

(* ----------------------------------------------------------------- *)
(** *** Тактикал [repeat] *)

(** Тактикал [repeat] принимает другую тактику и применяет её до тех пор, пока
    она не выбросит исключение, либо не завершится успешно, но ничего
    не сделает.

    Вот пример, доказывающий, что [10] содержится в длинном списке, использующий
    [repeat]. *)

Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.

(** [repeat] может зацикливаться. *)

Theorem repeat_loop : forall (m n : nat),
  m + n = n + m.
Proof.
  intros m n.
  (* Раскомментируйте следующую строчку, чтобы увидеть бесконечный цикл.
     Правда, после этого Вам нужно будет прервать исполнение, чтобы Rocq снова
     начал исполнять Ваши команды.  (В Proof General -- [C-c C-c].) *)
  (* repeat rewrite Nat.add_comm. *)
Admitted.

(* ================================================================= *)
(** ** Определение новых тактик *)

(** Rocq также предоставляет средства для "программирования" скриптов
    тактик:
     - [Ltac]: скриптовый язык для тактик (подходит для более замысловатого
       инжиниринга доказательств)
     - [Tactic Notation] для определения тактик с кастомным синтаксисом
     - API для скриптинга на OCaml (для продвинутых пользователей)

    [Ltac] покрывает все наши потребности на данный момент.

    Например: *)

Ltac invert H :=
  inversion H; subst; clear H.

(* ================================================================= *)
(** ** Тактика [lia] *)

(** Тактика [lia] реализует процедуру решения задач целочисленной линейной
    алгебры, подмножества пропозициональной логики и арифметики.

    Если цель -- формула под кванторами всеобщности, состоящая из

      - численных констант, сложений ([+] и [S]), вычитаний ([-] и [pred]) и
        умножений на константы (т.е. получается арифметика Пресбургера),

      - (не)равенств ([=] и [<>]) и сравнений ([<=] и [>]), и

      - логических связок [/\], [\/], [~], и [->],

    то вызов [lia] либо решит цель, либо выкинет ошибку, если цель на самом деле
    ложна. (Либо имеет не тот вид, который ожидает [lia].) *)

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. lia.
Qed.

Example add_comm__lia : forall m n,
    m + n = n + m.
Proof.
  intros. lia.
Qed.

Example add_assoc__lia : forall m n p,
    m + (n + p) = m + n + p.
Proof.
  intros. lia.
Qed.

(* ================================================================= *)
(** ** Ещё пара полезных тактик *)

(** Наконец, вот ещё несколько тактик, которые могут Вам пригодиться.

     - [clear H]: Удалить гипотезу [H] из контекста.

     - [subst x]: Найти вхождения [x = e] либо [e = x] в контекст (где [x] --
       переменная), заменить [x] на [e] в контексте и текущей цели и удалить
       гипотезу.

     - [subst]: Подставить _все_ гипотезы вида [x = e] и [e = x]
       (где [x] -- переменная).

     - [rename... into...]: Изменить имя гипотезы в контексте доказательства.
       Например, если контекст содержит переменную [x], то [rename x into y]
       заменит все вхождения [x] на [y].

     - [assumption]: Попытаться найти в контексте такую [H], которая в точности
       совпадает с целью; если такая [H] нашлось, решить цель.

     - [contradiction]: Попытаться найти в контексте [H], логически
       эквивалентную [False].  Если таковая найдена, решить цель.

     - [constructor]: Попытаться найти конструктор [c] (из какого-то
       [Индуктивного] определения в текущей области видимости), который можно
       применить для решения текущей цели.  Если таковой [c] найден,
       [constructor] ведёт себя как [apply c].

    По ходу дела мы увидим примеры применения каждой из них. *)

(* ################################################################# *)
(** * Вычисление как отношение *)

(** Мы представили [aeval] и [beval] в виде функций, определённых через
    [Fixpoint].  Другой способ думать о вычислении -- и зачастую более гибкий --
    как об _отношении_ между выражениями и их значениями.  Эта точка зрения
    приводит к определениям вроде следующего... *)

Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      aevalR (ANum n) n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

(** Стандартная нотация для "вычисляется в": *)

Notation "e '==>' n"
         := (aevalR e n)
            (at level 90, left associativity)
         : type_scope.

End aevalR_first_try.

(** С инфиксной нотацией: *)

Reserved Notation "e '==>' n" (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (APlus e1 e2)  ==> (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (AMinus e1 e2) ==> (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (AMult e1 e2)  ==> (n1 * n2)

  where "e '==>' n" := (aevalR e n) : type_scope.

(* ================================================================= *)
(** ** Нотация в виде правил вывода *)

(** В неформальных рассуждениях удобно выписывать правила для [aevalR] и похожих
    отношений в более читаемой графической записи _правил вывода_, где черта
    разделяет гипотезы (над линией) и заключения (под линией).

    Так, конструктор [E_APlus]...

      | E_APlus : forall (e1 e2 : aexp) (n1 n2 : nat),
          aevalR e1 n1 ->
          aevalR e2 n2 ->
          aevalR (APlus e1 e2) (n1 + n2)

    ...можно выписать в виде правила вывода следующим образом:

                               e1 ==> n1
                               e2 ==> n2
                         --------------------                (E_APlus)
                         APlus e1 e2 ==> n1+n2
*)

(** Ничего особо глубокого здесь не происходит:
      - набор правил вывода соответствует одному [Индуктивному] определению
      - каждое имя правила соответствует имени конструктора
      - над чертой выписаны гипотезы
      - под чертой -- заключение
      - _метапеременные_ вроде [e1] и [n1] неявно вводятся кванторами
        всеобщности
*)

(** Например, мы могли бы определить [==>] как наименьшее отношение, замкнутое
    относительно следующих правил:

                             -----------                               (E_ANum)
                             ANum n ==> n

                               e1 ==> n1
                               e2 ==> n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 ==> n1+n2

                               e1 ==> n1
                               e2 ==> n2
                        ---------------------                        (E_AMinus)
                        AMinus e1 e2 ==> n1-n2

                               e1 ==> n1
                               e2 ==> n2
                         --------------------                         (E_AMult)
                         AMult e1 e2 ==> n1*n2
*)

(* ================================================================= *)
(** ** Эквивалентность определений *)

(** Доказать, что определения через функцию и через отношение совпадают, просто:
*)

Theorem aevalR_iff_aeval : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.
  split.
  - (* -> *)
    intros H.
    induction H; simpl.
    + (* E_ANum *)
      reflexivity.
    + (* E_APlus *)
      rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
    + (* E_AMinus *)
      rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
    + (* E_AMult *)
      rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
  - (* <- *)
    generalize dependent n.
    induction a;
       simpl; intros; subst.
    + (* ANum *)
      apply E_ANum.
    + (* APlus *)
      apply E_APlus.
      * apply IHa1. reflexivity.
      * apply IHa2. reflexivity.
    + (* AMinus *)
      apply E_AMinus.
      * apply IHa1. reflexivity.
      * apply IHa2. reflexivity.
    + (* AMult *)
      apply E_AMult.
      * apply IHa1. reflexivity.
      * apply IHa2. reflexivity.
Qed.

(** Опять же, доказательство можно сильно упростить, используя тактикалы. *)

Theorem aevalR_iff_aeval' : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.
  (* РАЗБИРАЕМ НА ЛЕКЦИИ *) Admitted.

End AExp.

(* ================================================================= *)
(** ** Функции vs. отношения *)

(** Иногда определения через отношения -- единственный доступный
    вариант... *)

Module aevalR_division.

(* ----------------------------------------------------------------- *)
(** *** Добавим деление *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp).         (* <--- NEW *)

(** Что [aeval] должен вернуть на [ADiv (ANum 1) (ANum 0)]?? *)

(* ----------------------------------------------------------------- *)
(** *** А теперь добавим деление в отношение *)

Reserved Notation "e '==>' n"
                  (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (APlus a1 a2) ==> (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMinus a1 a2) ==> (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMult a1 a2) ==> (n1 * n2)
  | E_ADiv (a1 a2 : aexp) (n1 n2 n3 : nat) :          (* <----- NEW *)
      (a1 ==> n1) -> (a2 ==> n2) -> (n2 > 0) ->
      (mult n2 n3 = n1) -> (ADiv a1 a2) ==> n3

where "a '==>' n" := (aevalR a n) : type_scope.

(** Обратите внимание, что такое отношение вычислений соответствует _частичной_
    функции: есть такие выражения, для которых результат не определён. *)

End aevalR_division.

Module aevalR_extended.

(* ----------------------------------------------------------------- *)
(** *** Добавим недетерминизм *)

(** Другой пример: _недетерминированный_ генератор чисел: *)

Reserved Notation "e '==>' n" (at level 90, left associativity).

Inductive aexp : Type :=
  | AAny                           (* <--- NEW *)
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

(** Что [aeval] делать с недетерминизмом?? *)

(* ----------------------------------------------------------------- *)
(** *** Добавим недетерминизм в отношение *)

Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any (n : nat) :
      AAny ==> n                        (* <--- NEW *)
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (APlus a1 a2) ==> (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMinus a1 a2) ==> (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMult a1 a2) ==> (n1 * n2)

where "a '==>' n" := (aevalR a n) : type_scope.

End aevalR_extended.

(* ----------------------------------------------------------------- *)
(** *** Компромиссы *)

(** Какой стиль лучше, через функции или через отношения?

    - Функциональный: переиспользование движка вычислений Rocq.
    - Реляционный: более выразительный.
    - Лучшее из двух миров: определить оба и доказать эквивалентность.
*)

(* ################################################################# *)
(** * Выражения с переменными *)

(** Наконец вернёмся к определению Imp. Следующий пункт нашей программы --
    обогатить арифметические и логические выражения переменными.

    Для упрощения положим, что все переменные глобальные, и в них сохраняются
    только числа. *)

(* ================================================================= *)
(** ** Состояния *)

(** Поскольку мы хотим хранить и запрашивать текущие значения переменных, мы
    будем использовать тотальные словари из главы [Maps].

    _Состояние машины_ (либо просто _состояние_) представляет текущие значения
    всех переменных на некоторый момент исполнения программы. *)

Definition state := total_map nat.

(* ================================================================= *)
(** ** Синтаксис *)

(** Мы можем добавить переменные в арифметические выражения, которые мы
    определили ранее, включив ещё один конструктор: *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)              (* <--- NEW *)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

(** Определение некоторых переменных сделает наши примеры более читаемыми: *)

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

(** Определение [bexp]ов не меняется (разве что теперь мы ссылаемся на новое
    определение [aexp]): *)

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

(* ================================================================= *)
(** ** Нотации *)

(** Чтобы сделать программы на Imp проще для чтения и написания, мы введём
    несколько нотаций и неявных преобразований.  *)

(** (Детали не очень красивые, но их и не очень важно понимать.) *)

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e
  (e custom com, format "'[hv' <{ '/  ' '[v' e ']' '/' }> ']'") : com_scope.

Notation "( x )" := x (in custom com, x at level 99).
Notation "x" := x (in custom com at level 0, x constr at level 0).

Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 1,
                      y constr at level 1).
Notation "x + y"   := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y"   := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y"   := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y"   := (BGt x y) (in custom com at level 70, no associativity).
Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y"  := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).

Open Scope com_scope.

(** Теперь мы можем писать [3 + (X * 2)] вместо [APlus 3 (AMult X 2)],
    и [true && ~(X <= 4)] вместо [BAnd true (BNot (BLe X 4))]. *)

Definition example_aexp : aexp := <{ 3 + (X * 2) }>.
Definition example_bexp : bexp := <{ true && ~(X <= 4) }>.

(* ================================================================= *)
(** ** Вычисление *)

(** Теперь нам нужно добавить параметр [st] в обеих вычисляющих функциях:
*)

Fixpoint aeval (st : state) (* <--- NEW *)
               (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                (* <--- NEW *)
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (* <--- NEW *)
               (b : bexp) : bool :=
  match b with
  | <{true}>      => true
  | <{false}>     => false
  | <{a1 = a2}>   => (aeval st a1) =? (aeval st a2)
  | <{a1 <> a2}>  => negb ((aeval st a1) =? (aeval st a2))
  | <{a1 <= a2}>  => (aeval st a1) <=? (aeval st a2)
  | <{a1 > a2}>   => negb ((aeval st a1) <=? (aeval st a2))
  | <{~ b1}>      => negb (beval st b1)
  | <{b1 && b2}>  => andb (beval st b1) (beval st b2)
  end.

(** Мы можем использовать нашу нотацию для тотальных словарей и для состояний
    тоже -- т.е., записать пустое состояние как [(__ !-> 0)]. *)

Definition empty_st := (__ !-> 0).

(** Также, мы можем добавить нотацию для "состояния-синглетона", содержащего
    запись о единственной определённой переменной. *)
Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100, right associativity).

(* ################################################################# *)
(** * Команды *)

(** Теперь мы готовы определить синтаксис и поведение _команд_ Imp
    (либо _инструкций_). *)

(* ================================================================= *)
(** ** Синтаксис *)

(** Команды [c] описываются следующей BNF-грамматикой.

     c := skip
        | x := a
        | c ; c
        | if b then c else c end
        | while b do c end
*)

(** Формально: *)

Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

(** Как и для выражений, нам не помешает парочка [Нотаций] для более удобного
    чтения и написания программ на Imp. *)

(* SOON: (NOTATION NDS'25)
   I considered changing maps to also span multiple lines, but I
   have not attempted this yet, as this would have required changes
   in earlier chapters. *)
Notation "'skip'"  := CSkip
  (in custom com at level 0) : com_scope.
Notation "x := y"  := (CAsgn x y)
  (in custom com at level 0, x constr at level 0, y at level 85, no associativity,
    format "x  :=  y") : com_scope.
Notation "x ; y" := (CSeq x y)
  (in custom com at level 90,
    right associativity,
    format "'[v' x ; '/' y ']'") : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" := (CIf x y z)
  (in custom com at level 89, x at level 99, y at level 99, z at level 99,
    format "'[v' 'if'  x  'then' '/  ' y '/' 'else' '/  ' z '/' 'end' ']'") : com_scope.
Notation "'while' x 'do' y 'end'" := (CWhile x y)
  (in custom com at level 89, x at level 99, y at level 99,
    format "'[v' 'while'  x  'do' '/  ' y '/' 'end' ']'") : com_scope.

(** Например, вот снова функция факториала на Imp, выписанная в Rocq. Когда эта
    команда завершится, переменная [Y] будет содержать значение факториала
    начального значения [X]. *)

Definition fact_in_coq : com :=
  <{ Z := X;
     Y := 1;
     while Z <> 0 do
       Y := Y * Z;
       Z := Z - 1
     end }>.

Print fact_in_coq.

(* ================================================================= *)
(** ** Больше примеров *)

(* ----------------------------------------------------------------- *)
(** *** Присваивания: *)

Definition plus2 : com :=
  <{ X := X + 2 }>.

Definition XtimesYinZ : com :=
  <{ Z := X * Y }>.

(* ----------------------------------------------------------------- *)
(** *** Циклы *)

Definition subtract_slowly_body : com :=
  <{ Z := Z - 1 ;
     X := X - 1 }>.

Definition subtract_slowly : com :=
  <{ while X <> 0 do
       subtract_slowly_body
     end }>.

Definition subtract_3_from_5_slowly : com :=
  <{ X := 3 ;
     Z := 5 ;
     subtract_slowly }>.

(* ----------------------------------------------------------------- *)
(** *** Бесконечный цикл: *)

Definition loop : com :=
  <{ while true do
       skip
     end }>.

(* ################################################################# *)
(** * Исполнение команд *)

(** Далее нам нужно определить, что значит исполнить команду на языке Imp.
    Тот факт, что циклы [while] не обязательно завершаются, делает определение
    функции вычисления непростым делом... *)

(* ================================================================= *)
(** ** Исполнение как функция (провал) *)

(** Вот попытка определить функцию исполнения команд
    (с бредовым случаем для [while]). *)

Fixpoint ceval_fun_no_while (st : state) (c : com) : state :=
  match c with
    | <{ skip }> =>
        st
    | <{ x := a }> =>
        (x !-> aeval st a ; st)
    | <{ c1 ; c2 }> =>
        let st' := ceval_fun_no_while st c1 in
        ceval_fun_no_while st' c2
    | <{ if b then c1 else c2 end}> =>
        if (beval st b)
          then ceval_fun_no_while st c1
          else ceval_fun_no_while st c2
    | <{ while b do c end }> =>
        st  (* бредово *)
  end.

(* ----------------------------------------------------------------- *)
(** *** Не-завершение приводит к противоречию

    Рассмотрим следующий "объект доказательства":

        Fixpoint loop_false (n : nat) : False := loop_false n.

    Принятие такого определения было бы катастрофой, так что Rocq консервативно
    отвергает _все_ не завершающиеся (и потенциально не завершающиеся,
    и не-очевидно-что-завершающиеся) программы.
*)

(* ================================================================= *)
(** ** Исполнение как отношение *)

(** Вот способ получше: определить [ceval] как _отношение_, а не как _функцию_
    -- т.е., сделать её результатом [Prop] вместо [state], как мы уже делали
    с [aevalR] выше. *)

(** Для отношения [ceval] мы будем использовать нотацию [st =[ c ]=> st']: она
    значит, что исполнение программы [c] из начального состояния [st] приводит
    в конечное состояние [st'].  Можно читать как
    "[c] отправляет состояние [st] в [st']". *)

(* ----------------------------------------------------------------- *)
(** *** Операционная семантика *)

(** Вот "бумажное" определение вычисления, представленное в виде правил вывода:

                           -----------------                            (E_Skip)
                           st =[ skip ]=> st

                           aeval st a = n
                   -------------------------------                      (E_Asgn)
                   st =[ x := a ]=> (x !-> n ; st)

                           st  =[ c1 ]=> st'
                           st' =[ c2 ]=> st''
                         ---------------------                           (E_Seq)
                         st =[ c1;c2 ]=> st''

                          beval st b = true
                           st =[ c1 ]=> st'
                --------------------------------------               (E_IfTrue)
                st =[ if b then c1 else c2 end ]=> st'

                         beval st b = false
                           st =[ c2 ]=> st'
                --------------------------------------              (E_IfFalse)
                st =[ if b then c1 else c2 end ]=> st'

                         beval st b = false
                    -----------------------------                 (E_WhileFalse)
                    st =[ while b do c end ]=> st

                          beval st b = true
                           st =[ c ]=> st'
                  st' =[ while b do c end ]=> st''
                  --------------------------------                 (E_WhileTrue)
                  st  =[ while b do c end ]=> st''
*)

Reserved Notation
         "st0 '=[' c ']=>' st1"
         (at level 40, c custom com at level 99,
          st0 constr, st1 constr at next level,
          format "'[hv' st0  =[ '/  ' '[' c ']' '/' ]=>  st1 ']'").

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''

  where "st0 =[ c ]=> st1" := (ceval c st0 st1).
(** Цена определения вычисления через отношение (а не через функцию):
    теперь нам нужно строить _доказательство_ того, что программа исполняет
    переход в некоторое состояние, и положиться в этом на механизм вычислений
    Rocq мы не можем. *)

Example ceval_example1:
  empty_st =[
     X := 2;
     if (X <= 1)
       then Y := 3
       else Z := 4
     end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  (* Мы должны предоставить промежуточное состояние *)
  apply E_Seq with (X !-> 2).
  - (* инструкция присваивания *)
    apply E_Asgn. reflexivity.
  - (* условный переход *)
    apply E_IfFalse.
    + reflexivity.
    + apply E_Asgn. reflexivity.
Qed.

(** Какого рода утверждения мы можем захотеть доказать,
    используя эти определения?

    Вот пара простых примеров...
*)
(* QUIZ

    Доказуемо ли следующее утверждение?

      forall (c : com) (st st' : state),
        st =[ skip ; c ]=> st' ->
        st =[ c ]=> st'

    (A) Да

    (B) Нет

    (C) Не уверен

*)
(* QUIZ

    Доказуемо ли следующее утверждение?

      forall (c1 c2 : com) (st st' : state),
          st =[ c1 ; c2 ]=> st' ->
          st =[ c1 ]=> st ->
          st =[ c2 ]=> st'

    (A) Да

    (B) Нет

    (C) Не уверен

*)
(* QUIZ

    Доказуемо ли следующее утверждение?

      forall (b : bexp) (c : com) (st st' : state),
          st =[ if b then c else c end ]=> st' ->
          st =[ c ]=> st'

    (A) Да

    (B) Нет

    (C) Не уверен

*)
(* QUIZ

    Доказуемо ли следующее утверждение?

      forall b : bexp,
         (forall st, beval st b = true) ->
         forall (c : com) (st : state),
           ~(exists st', st =[ while b do c end ]=> st')

    (A) Да

    (B) Нет

    (C) Не уверен

*)
(* QUIZ

    Доказуемо ли следующее утверждение?

      forall (b : bexp) (c : com) (st : state),
         ~(exists st', st =[ while b do c end ]=> st') ->
         forall st'', beval st'' b = true

    (A) Да

    (B) Нет

    (C) Не уверен

*)

(* ================================================================= *)
(** ** Детерминированность вычислений *)

(** Наконец, нам следует сделать остановку и проверить, является ли наше
    вычисление (частичной) функцией... *)

Theorem ceval_deterministic: forall c st st1 st2,
     st =[ c ]=> st1  ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Asgn *) reflexivity.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    apply IHE1_2. assumption.
  - (* E_IfTrue, b evaluates to true *)
      apply IHE1. assumption.
  - (* E_IfTrue,  b evaluates to false (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to true (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to false *)
      apply IHE1. assumption.
  - (* E_WhileFalse, b evaluates to false *)
    reflexivity.
  - (* E_WhileFalse, b evaluates to true (contradiction) *)
    rewrite H in H2. discriminate.
  - (* E_WhileTrue, b evaluates to false (contradiction) *)
    rewrite H in H4. discriminate.
  - (* E_WhileTrue, b evaluates to true *)
    rewrite (IHE1_1 st'0 H3) in *.
    apply IHE1_2. assumption.  Qed.

(* ################################################################# *)
(** * Дополнительные упражнения *)

(** **** Упражнение: 3 звезды, стандартное (stack_compiler)

    Старые калькуляторы фирмы HP, языки программирования Forth и Postscript,
    а также абстрактные машины вроде Виртуальной машины Java вычисляют
    арифметические выражения с помощью _стека_. Например, выражение

      (2*3)+(3*(4-2))

    можно записать в обратной польской записи как

      2 3 * 3 4 2 - * +

    и вычислить следующим образом (где мы показываем исполняемую программу
    справа, а содержимое стека -- слева):

      [ ]           |    2 3 * 3 4 2 - * +
      [2]           |    3 * 3 4 2 - * +
      [3, 2]        |    * 3 4 2 - * +
      [6]           |    3 4 2 - * +
      [3, 6]        |    4 2 - * +
      [4, 3, 6]     |    2 - * +
      [2, 4, 3, 6]  |    - * +
      [2, 3, 6]     |    * +
      [6, 6]        |    +
      [12]          |

    Цель данного упражнения -- написать маленький компилятор, переводящий
    [aexp]ы в инструкции для стековой машины.
,
    Набор инструкций нашего стекового языка будет следующим:
      - [SPush n]: Положить [n] на вершину стека.
      - [SLoad x]: Загрузить идентификатор [x] из хранилища и положить
                   на вершину стека.
      - [SPlus]:   Забрать два верхних числа с вершины стека, сложить их,
                   и положить результат обратно на вершину стека.
      - [SMinus]:  Аналогично [SPlus], но не сложить числа,
                   а вычесть первое число из второго.
      - [SMult]:   Аналогично [SPlus], но не сложить числа, а перемножить. *)

Inductive sinstr : Type :=
| SPush (n : nat)
| SLoad (x : string)
| SPlus
| SMinus
| SMult.

(** Напишите функцию для исполнения программ стекового языка. Она должна
    принимать состояние (стек, представленный списком чисел, где голова
    списка -- вершина стека) и программу, представленную списком инструкций,
    и должна возвращать состояние стека после исполнения программы.
    Протестируйте Вашу функцию на примерах ниже.

    Обратите внимание, что в условии не указано, что делать, если нужно
    исполнить [SPlus], [SMinus] или [SMult], а в стеке меньше двух элементов.
    В каком-то смысле неважно, что делать в таком случае, ведь корректный
    компилятор никогда не сгенерирует некорректную программу.  Но для простоты
    решения последующих упражнений лучше всего будет пропустить некорректную
    инструкцию и продолжить со следующей.  *)

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat
  (* ЗАМЕНИТЕ ЭТУ СТРОЧКУ НА ":= _ваше_определение_ ." *). Admitted.

Check s_execute.

Example s_execute1 :
     s_execute empty_st []
       [SPush 5; SPush 3; SPush 1; SMinus]
   = [2; 5].
(* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Example s_execute2 :
     s_execute (X !-> 3) [3;4]
       [SPush 4; SLoad X; SMult; SPlus]
   = [15; 4].
(* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

(** Далее, напишите функцию, компилирующую [aexp] в программу для стековой
    машины. Эффект от работы программы должен быть таким же, как при
    выкладывании значения выражения на верхушку стека. *)

Fixpoint s_compile (e : aexp) : list sinstr
  (* ЗАМЕНИТЕ ЭТУ СТРОЧКУ НА ":= _ваше_определение_ ." *). Admitted.

(** После того, как Вы определили [s_compile], докажите следующее утверждение,
    чтобы проверить, что Ваше определение работает. *)

Example s_compile1 :
  s_compile <{ X - (2 * Y) }>
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
(* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
(** [] *)

(** **** Упражнение: 3 звезды, стандартное (execute_app) *)

(** Исполнение можно декомпозировать в следующем смысле: исполнение стековой
    программы [p1 ++ p2] такое же, как у последовательного исполнения сначала
    [p1], а затем [p2]. Докажите этот факт. *)

Theorem execute_app : forall st p1 p2 stack,
  s_execute st stack (p1 ++ p2) = s_execute st (s_execute st stack p1) p2.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

(** [] *)

(** **** Упражнение: 3 звезды, стандартное (stack_compiler_correct) *)

(** Теперь мы докажем _корректность_ компилятора, реализованного в предыдущем
    упражнении.  Начните с доказательства следующей леммы. Если становится
    сложно, подумайте, можно ли упростить Вашу реализацию [s_execute] либо
    [s_compile]. *)

Lemma s_compile_correct_aux : forall st e stack,
  s_execute st stack (s_compile e) = aeval st e :: stack.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

(** Основная теорема становится очень простым следствием из леммы. *)

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

(** [] *)

