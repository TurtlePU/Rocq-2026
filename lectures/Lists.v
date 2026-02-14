(** * Списки: Работа со структурированными данными *)

From Lectures Require Export Induction.
Module NatList.

(* ################################################################# *)
(** * Пары натуральных чисел *)

(** [Индуктивное] определение пары натуральных чисел.  В нём объявлен
    тольно один конструктор от двух аргументов: *)

Inductive natprod : Type :=
  | pair (n1 n2 : nat).

Check (pair 3 5) : natprod.

(** Функции для извлечения первой и второй компонент пары можно определить
    через сопоставление с образцом. *)

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).
(* ===> 3 *)

(** Более привычная нотация для пар: *)

Notation "( x , y )" := (pair x y).

(** Нотации можно использовать как в выражениях,
    так и в сопоставлениях с образцом. *)

Compute (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

(** Если мы будем формулировать свойства пар несколько обходным путём, мы иногда
    сможем завершить их доказательства лишь с помощью [рефлексивности] и
    встроенных упрощений: *)

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity. Qed.

(** Однако просто [рефлексивности] недостаточно, если мы сформулируем
    утверждение леммы естественным образом: *)

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* Ничего не упрощает! *)
Abort.

(** Решение: использовать [destruct]. *)

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

(* ################################################################# *)
(** * Списки натуральных чисел *)

(** Индуктивное определение _списков_ чисел: *)

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

(** Немного нотаций для списков, чтобы упростить нам жизнь: *)

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(** Теперь все записи ниже обозначают один и тот же список: *)

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

(** Щепотка полезных в работе со списками функций... *)

(* ----------------------------------------------------------------- *)
(** *** Повтор элемента *)

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

(* ----------------------------------------------------------------- *)
(** *** Длина списка *)

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

(* ----------------------------------------------------------------- *)
(** *** Конкатенация *)

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1:             [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2:             nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3:             [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(** *** Голова и хвост *)

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1:             hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2:             hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl:              tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

(* QUIZ

    Что делает следующая функция? *)

Fixpoint foo (n : nat) : natlist :=
  match n with
  | 0 => nil
  | S n' => n :: (foo n')
  end.

(* ################################################################# *)
(** * Доказательство теорем о списках *)

(** Как и с числами, некоторым доказательствам о списках достаточно
    упрощений... *)

Theorem nil_app : forall l : natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

(** ...другим же нужен разбор по случаям. *)

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity.  Qed.

(** Правда, чаще всего, доказательство интересных теорем о списках требует
    использования _индукции по спискам_.  Сейчас мы увидим, как это делать. *)

(* ================================================================= *)
(** ** Индукция на списках *)

(** Rocq генерирует принцип индукции для каждого [Индуктивного]
    определения, включая списки.  Так, можно использовать тактику [induction]
    на списках, чтобы доказать, например, ассоциативность конкатенации... *)

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(** Для сравнения, вот неформальное (но строгое) доказательство той же самой
    теоремы. *)

(** _Теорема_: Для любых [l1], [l2] и [l3] верно, что
               [(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)].

   _Доказательство_: Индукцией по [l1].

   - База: [l1 = []].  Нужно показать, что

       ([] ++ l2) ++ l3 = [] ++ (l2 ++ l3),

     что верно по определению [++].

   - Переход: [l1 = n::l1'], причём по предположению индукции

       (l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3).

     Необходимо показать

       ((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ (l2 ++ l3).

     По определению [++], это следует из

       n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3)),

     что также верно благодаря предположению индукции.  [] *)

(* ----------------------------------------------------------------- *)
(** *** Усиление индукционной гипотезы *)

(** Иногда утверждения требуется усилять, чтобы доказать их по индукции:
*)

Theorem repeat_double_firsttry : forall c n: nat,
  repeat n c ++ repeat n c = repeat n (c + c).
Proof.
  intros c. induction c as [| c' IHc'].
  - (* c = 0 *)
    intros n. simpl. reflexivity.
  - (* c = S c' *)
    intros n. simpl.
    (*  Здесь-то мы, кажется, и застряли.  Мы не можем использовать IH, чтобы
        переписать [repeat n (c' + S c')]: гипотеза работает только для
        [repeat n (c' + c')]. Если бы IH была более гибкой (например, если бы
        она работала для произвольного второго слагаемого), доказательство бы
        прошло. *)
Abort.

(** Обобщение утверждения, приводящее к более сильному предположению
    индукции: *)

Theorem repeat_plus: forall c1 c2 n: nat,
    repeat n c1 ++ repeat n c2 = repeat n (c1 + c2).
Proof.
  intros c1 c2 n.
  induction c1 as [| c1' IHc1'].
  - simpl. reflexivity.
  - simpl.
    rewrite <- IHc1'.
    reflexivity.
  Qed.

(* ----------------------------------------------------------------- *)
(** *** Развороты списка *)

(** Более интересный пример индукции на списках: *)

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.

Example test_rev1:            rev [1;2;3] = [3;2;1].
Proof. reflexivity.  Qed.
Example test_rev2:            rev nil = nil.
Proof. reflexivity.  Qed.

(** Попробуем доказать, что [length (rev l) = length l]. *)

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = n :: l' *)
    simpl.
    rewrite <- IHl'.
Abort.

(** Первая попытка: *)
Theorem app_rev_length_S_firsttry: forall l n,
  length (rev l ++ [n]) = S (length (rev l)).
Proof.
  intros l. induction l as [| m l' IHl'].
  - (* l = [] *)
    intros n. simpl. reflexivity.
  - (* l = m:: l' *)
    intros n. simpl.
    (* IHl' применить нельзя. *)
Abort.

(** Немного усиленное утверждение: *)
Theorem app_length_S: forall l n,
  length (l ++ [n]) = S (length l).
Proof.
  intros l n. induction l as [| m l' IHl'].
  - (* l = [] *)
    simpl. reflexivity.
  - (* l = m:: l' *)
    simpl.
    rewrite IHl'.
    reflexivity.
Qed.

(** Теперь мы можем закончить основное доказательство. *)

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl.
    rewrite -> app_length_S.
    rewrite -> IHl'.
    reflexivity.
Qed.

(** Также мы можем доказать более общую форму [app_length_S],
    для конкатенации произвольных списков. *)
Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* РАЗБИРАЕМ НА ЛЕКЦИИ *) Admitted.

(* QUIZ

    Чтобы доказать следующую теорему, какие тактики нужны помимо [intros],
    [simpl], [rewrite] и [reflexivity]?  (A) никаких, (B) [destruct],
    (C) [induction on n], (D) [induction on l] или (E) известных нам тактик
    недостаточно для доказательства.

      Theorem foo1 : forall n:nat, forall l:natlist,
        repeat n 0 = l -> length l = 0.
*)

(* QUIZ

    Как насчёт этой?

      Theorem foo2 :  forall n m : nat,
        length (repeat n m) = m.

    Какие тактики нужны помимо [intros], [simpl], [rewrite] и [reflexivity]?
    (A) никаких, (B) [destruct], (C) [induction on n], (D) [induction on m] или
    (E) известных нам тактик недостаточно для доказательства. *)

(* ################################################################# *)
(** * Частичные значения *)

(** Допустим, нам нужна функция, возвращающая [n]-й элемент списка. Но
    что делать, если список слишком короткий? *)

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42
  | a :: l' => match n with
               | 0 => a
               | S n' => nth_bad l' n'
               end
  end.

(** Решение: вернуть [natoption]. *)

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

End NatList.

(* ################################################################# *)
(** * Частичные функции *)

(** В качестве последней иллюстрации того, как можно определять типы данных в
    Rocq, ниже мы введём тип данных _частичных функций_, аналогичный
    ассоциативным массивам (aka словарям), которые легко найти в любом другом
    языке программирования. *)

(** Во-первых, определим новый индуктивный тип данных [id], который будет
    выступать в качестве "ключей" в наших словарях. *)

Inductive id : Type :=
  | Id (n : nat).

(** Внутри [id] лежит просто число.  Введение отдельного типа данных,
    оборачивающего каждое число в тэг [Id], делает определения более читаемыми
    и дарит нам гибкость в позднейшем изменении внутреннего представления [Id],
    если впоследствии нам это потребуется. *)

(** Также мы захотим проверять [id] на равенство: *)

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

(** **** Упражнение: 1 звезда, стандартное (eqb_id_refl) *)
Theorem eqb_id_refl : forall x, eqb_id x x = true.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
(** [] *)

(** Далее, определим тип частичных функций: *)

Module PartialMap.
Export NatList.  (* сделаем доступными определения из NatList *)

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

(** Функция [update] перегружает запись для данного ключа в словаре с помощью
    перекрытия старого определения новым (либо просто добавляет новую запись,
    если такого ключа ещё нет). *)

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

(** Мы можем определять функции на [partial_map]-ах с помощью
    сопоставления с образцом. *)

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty         => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.

(* QUIZ

    Верно ли следующее утверждение? *)

Theorem quiz1 : forall (d : partial_map)
                       (x : id) (v: nat),
  find x (update d x v) = Some v.

Proof.
(* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

(** (A) Да

    (B) Нет

    (C) Не уверен
*)

(* QUIZ

    Верно ли следующее утверждение? *)

Theorem quiz2 : forall (d : partial_map)
                       (x y : id) (o: nat),
  eqb_id x y = false ->
  find x (update d y o) = find x d.
Proof.
(* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

(** (A) Да

    (B) Нет

    (C) Не уверен
*)

End PartialMap.

