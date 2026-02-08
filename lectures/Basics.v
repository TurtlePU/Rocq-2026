(** * Основы: Функциональное программирование на Rocq *)

(* ################################################################# *)
(** * Типы данных и функции *)

(* ================================================================= *)
(** ** Типы-перечисления *)

(** В Rocq практически всё можно выстроить с нуля, "из аксиом". *)

(* ================================================================= *)
(** ** Дни недели *)

(** Определение типа данных: *)

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

(** Функция, действующая на днях: *)

Definition next_working_day (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

(** Выражения можно упрощать по заданным правилам: *)

Compute (next_working_day friday).
(* ==> monday : day *)

Compute (next_working_day (next_working_day saturday)).
(* ==> tuesday : day *)

(** Также мы можем записать, какой результат мы ожидаем получить
    в виде т.н. [Примеров]: *)

Example test_next_working_day:
  (next_working_day (next_working_day saturday)) = tuesday.

(** К каждому примеру нужно предоставить скрипт доказательства,
    предоставляющий свидетельство истинности заявленного утверждения: *)

Proof. simpl. reflexivity.  Qed.

(** А ещё мы можем попросить у Rocq _извлечь_ из нашего [Определения]
    программу, написанную в языке с более производительным компилятором.
    Обычно для этих целей выбирают OCaml, Scheme или Haskell.  Таким образом,
    мы можем получать крайне эффективный машинный код, про который была
    доказана корректность его работы.

    (Конечно, здесь мы принимаем на веру корректность работы компилятора
    OCaml/Haskell/Scheme, а также корректность самого механизма извлечения
    кода, но это уже большой шаг вперёд по сравнению с тем, как разрабатывают
    абсолютное большинство софта!) *)

(* ================================================================= *)
(** ** Логические значения *)

(** Ещё один знакомый тип-перечисление: *)

Inductive bool : Type :=
  | true
  | false.

(** Он, конечно, доступен в стандартной библиотеке Rocq, но в этом
    курсе мы будем вводить все определения с нуля, чтобы разобраться, как всё
    устроено. *)
Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

(** Обратите внимание на синтаксис, использованный для определения
    функций с несколькими аргументами ([andb] и [orb]).  *)
Example test_orb1:  (orb true  false) = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb2:  (orb false false) = false.
Proof. simpl. reflexivity.  Qed.
Example test_orb3:  (orb false true)  = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb4:  (orb true  true)  = true.
Proof. simpl. reflexivity.  Qed.

(** Также можно вводить новые [Нотации] для существующих определений.
*)

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5:  false || false || true = true.
Proof. simpl. reflexivity. Qed.

(** Также мы могли бы определить эти функции с помощью [if].  *)

Definition negb' (b:bool) : bool :=
  if b then false
  else true.

Definition andb' (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.

Definition orb' (b1:bool) (b2:bool) : bool :=
  if b1 then true
  else b2.

(** [if] сработает с любым типом данных с двумя конструкторами: *)

Inductive bw : Type :=
  | bw_black
  | bw_white.

Definition invert (x: bw) : bw :=
  if x then bw_white
  else bw_black.

Compute (invert bw_black).
(* ==> bw_white : bw *)

Compute (invert bw_white).
(* ==> bw_black : bw *)

(** **** Упражнение: 1 звезда, стандартное (nandb) *)

Definition nandb (b1:bool) (b2:bool) : bool
  (* ЗАМЕНИТЕ ЭТУ СТРОЧКУ НА ":= _ваше_определение_ ." *). Admitted.

Example test_nandb1:               (nandb true false) = true.
(* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
Example test_nandb2:               (nandb false false) = true.
(* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
Example test_nandb3:               (nandb false true) = true.
(* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
Example test_nandb4:               (nandb true true) = false.
(* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
(** [] *)

(** Большинства других упражнений в лекционных файлах не будет.

    Упражнения будут содержаться в отдельных файлах для домашних заданий
    вместе с кодом с лекций и необходимыми пояснениями. *)

(* ================================================================= *)
(** ** Типы *)

(** Каждое выражение в Rocq имеет тип, описывающий, какого сорта значение оно
    вычисляет. Команда [Check] просит у Rocq распечатать тип выражения. *)

Check true.
(* ===> true : bool *)

(** Если аргумент [Check] проаннотирован типом, Rocq заодно проверит, что тип
    выражения сходится с указанным, и сообщит об ошибке, если это не так. *)

Check true
  : bool.
Check (negb true)
  : bool.

(** Функции вроде [negb] -- тоже значения, точно такие же, как [true] и
    [false].  Типы функций пишутся с помощью стрелок. *)

Check negb
  : bool -> bool.

(* ================================================================= *)
(** ** Новые типы на основе старых *)

(** Чуть более интересное определение типа: *)

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

(** Давайте посмотрим чуть внимательнее.

    [Индуктивное] определение делает две вещи:

    - Вводит несколько новых _конструкторов_. Так, [red], [primary], [true],
      [false], [monday] являются конструкторами.

    - Группирует конструкторы в новый именованный тип, вроде
      [bool], [rgb] и [color].

    _Конструкторные выражения_ получаются применением конструктора к
    некоторому числу других конструкторных выражений, в соответствии с типами
    конструктора и его аргументов.
    Примеры правильных конструкторных выражений:
        - [red]
        - [true]
        - [primary red]
    Примеры НЕправильных конструкторных выражений:
        - [red primary]
        - [true red]
        - [primary (primary red)]
*)

(** Определим функции, действующие на цветах, с помощью сопоставления с
    образцом -- в точности так же, как мы это делали для дней недели и
    логических значений. *)

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary x => false
  end.

(** Раз конструктор [primary] принимает аргумент, образец, сопоставляемый
    [primary], должен включать либо переменную, как мы сделали выше (обратите
    внимание, что имя [x] выбрано произвольно), либо другой паттерн
    подходящего типа (как ниже). *)

Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

(** Паттерн "[primary _]" здесь значит "конструктор [primary], применённый к
    любому конструктору типа [rgb], кроме [red]." *)

(* ================================================================= *)
(** ** Модули *)

(** Объявления [Модулей] создают отдельные пространства имён. *)

Module Playground.
  Definition foo : rgb := blue.
End Playground.

Definition foo : bool := true.

Check Playground.foo : rgb.
Check foo : bool.

(* ================================================================= *)
(** ** Кортежи *)

Module TuplePlayground.

(** nybble (nibble) -- полубайт, т.е. четыре бита. *)

Inductive bit : Type :=
  | B1
  | B0.

Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0)
  : nybble.

(** Мы можем получить доступ к внутренностям полубайта с помощью
    сопоставления с образцом. *)

Definition all_zero (nb : nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | (bits _ _ _ _) => false
  end.

(** (Нижнее подчёркивание (_) -- _паттерн-джокер_, с помощью которого не нужно
    выдумывать имена переменных, которые потом всё равно не будут
    использоваться.) *)

Compute (all_zero (bits B1 B0 B1 B0)).
(* ===> false : bool *)
Compute (all_zero (bits B0 B0 B0 B0)).
(* ===> true : bool *)

End TuplePlayground.

(* ================================================================= *)
(** ** Числа *)

Module NatPlayground.

(** У натуральных чисел много представлений: Вы наверняка знакомы с
    десятичной, шестнадцатеричной, восьмеричной и бинарной системами
    счисления. Для простоты доказательств мы будем использовать унарную:
    [O] будет обозначать ноль, а [S] представляет добавление ещё одной цифры
    "1".  Другими словами, [S] это операция "взятия следующего", которая,
    будучи применена к представлению [n], возвращает представление [n+1]. *)

Inductive nat : Type :=
  | O
  | S (n : nat).

(** Таким образом, 0 представляется как [O], 1 как [S O], 2 как [S (S O)]
    и т.д.. *)

(** Если быть чуть формальнее, то определение [nat] задаёт, как можно
    строить значения типа [nat]:

    - конструкторное выражение [O] принадлежит множеству [nat];
    - если [n] -- конструкторное выражение из множества [nat], то [S n] --
      тоже конструкторное выражение из множества [nat]; и
    - конструкторные выражения, построенные таким способом -- единственные,
      принадлежащие множеству [nat]. *)

(** Важно: это лишь _представление_ чисел -- унарная нотация для их
    записи.

    Имена [O] и [S] выбраны произвольно. Это лишь две различных "метки" без
    самостоятельного внутреннего значения.

    Мы точно так же могли бы выбрать другие метки для чисел: *)

Inductive otherNat : Type :=
  | stop
  | tick (foo : otherNat).

(** А вот _интерпретация_ этих меток возникает тогда, когда мы начинаем
    использовать их для вычислений. *)

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

End NatPlayground.

(** Для удобства, привычная десятичная запись используется в качестве
    сокращения для последовательностей применений [S] к [O]; Rocq использует то
    же самое сокращение для печати: *)

Check (S (S (S (S O)))).
(* ===> 4 : nat *)

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Compute (minustwo 4).
(* ===> 2 : nat *)

(** Рекурсивные функции вводятся с помощью ключевого слова [Fixpoint]. *)

Fixpoint even (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => even n'
  end.

(** Мы могли бы определить [odd] похожим объявлением [Fixpoint], но теперь есть
    способ проще: *)

Definition odd (n:nat) : bool :=
  negb (even n).

Example test_odd1:    odd 1 = true.
Proof. simpl. reflexivity.  Qed.
Example test_odd2:    odd 4 = false.
Proof. simpl. reflexivity.  Qed.

Module NatPlayground2.

(** Естественно, рекурсией также можно определить функцию от нескольких
    аргументов. *)

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Compute (plus 3 2).
(* ===> 5 : nat *)

(*      [plus 3 2]
   т.е. [plus (S (S (S O))) (S (S O))]
    ==> [S (plus (S (S O)) (S (S O)))]
          по второму случаю в [match]
    ==> [S (S (plus (S O) (S (S O))))]
          по второму случаю в [match]
    ==> [S (S (S (plus O (S (S O)))))]
          по второму случаю в [match]
    ==> [S (S (S (S (S O))))]
          по первому случаю в [match]
   т.е. [5]  *)

(** Ещё: *)

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity.  Qed.

(** Мы можем сопоставлять с образцом сразу несколько значений: *)

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O   , _    => O
  | S _ , O    => n
  | S n', S m' => minus n' m'
  end.

End NatPlayground2.

(** И вновь мы можем сделать числовые выражения более читаемыми с помощью новых
    нотаций для сложения, вычитания и умножения. *)

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Check ((0 + 1) + 1) : nat.

(** Когда мы говорим, что в Rocq практически ничего не встроено по умолчанию,
    мы действительно так считаем: даже проверка на равенство определена на
    уровне библиотеки!

    Вот, например, функция [eqb], проверяющая числа на равенство ([eq]) и
    возвращающая логическое значение ([b]) в качестве результата.
    Обратите внимание на вложенные конструкции [match] -- вместо этого мы могли
    бы сопоставлять по образцу оба числа сразу, как в [minus]. *)

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

(** Аналогично, функция [leb] проверяет, действительно ли первый аргумент не
    больше второго, и возвращает логическое значение. *)

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Example test_leb1:                leb 2 2 = true.
Proof. simpl. reflexivity.  Qed.
Example test_leb2:                leb 2 4 = true.
Proof. simpl. reflexivity.  Qed.
Example test_leb3:                leb 4 2 = false.
Proof. simpl. reflexivity.  Qed.

(** Мы будем часто пользоваться этими операциями (особенно [eqb]), так что
    давайте дадим им инфиксные нотации. *)

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity.  Qed.

(** Обратите внимание, что у нас есть два разных понятия равенства:

    - [=] это _утверждение_, которое мы можем попытаться _доказать_.

    - [=?] это логическое _выражение_ которое Rocq _вычисляет_.  *)

(* ################################################################# *)
(** * Доказательство упрощением *)

(** Достаточно частный факт о натуральных числах: *)
Example plus_1_1 : 1 + 1 = 2.
Proof. simpl. reflexivity. Qed.

(** А вот свойство чуть более общее: *)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity.  Qed.

(** Тактика [simpl] здесь на самом деле не нужна, так как [reflexivity]
    уже выполняет упрощения за нас: *)

Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

(** Любое другое (новое) имя можно использовать в доказательстве вместо
    [n]: *)

Theorem plus_O_n'' : forall n : nat, 0 + n = n.
Proof.
  intros m. reflexivity. Qed.

(** Другие похожие теоремы можно доказать аналогичным образом. *)

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity.  Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity.  Qed.

(* ################################################################# *)
(** * Доказательства переписыванием *)

(** (Немногим) более интересная теорема: *)

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.

Proof.
  (* вводим обе переменные в контекст: *)
  intros n m.
  (* перемещаем гипотезу в контекст: *)
  intros H.
  (* переписываем цель с помощью гипотезы: *)
  rewrite -> H.
  reflexivity.  Qed.

(** Использования [intros] называют гипотезы по мере того, как они
    перемещаются в контекст. Тактике [rewrite] нужно знать, какое равенство
    используется -- и в каком направлении -- чтобы выполнить переписывание. *)

(** Команду [Check] также можно использовать, чтобы изучить утверждения лемм и
    теорем, объявленных ранее. Ниже мы выясняем, что утверждают две леммы из
    стандартной библиотеки. (В следующий раз мы узнаем, как самим доказывать
    такие леммы.) *)

Check mult_n_O.
(* ===> forall n : nat, 0 = n * 0 *)

Check mult_n_Sm.
(* ===> forall n m : nat, n * m + n = n * S m *)

(** Тактику [rewrite] можно использовать не только с гипотезами из контекста, но
    и с ранее доказанными теоремами. Если при этом в утверждении теоремы
    содержатся кванторы, то, как в примере ниже, Rocq постарается подобрать для
    них подходящие значения с помощью сопоставления утверждения теоремы с
    текущей целью. *)

Theorem mult_n_0_m_0 : forall p q : nat,
  (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. Qed.

(* ################################################################# *)
(** * Доказательство разбором случаев *)

(** Иногда просто упрощений и переписываний оказывается недостаточно...*)

Theorem plus_1_neq_0_firsttry : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
  simpl.  (* ничего не делает! *)
Abort.

(** Мы можем использовать [destruct] для разбора случаев: *)

Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity.   Qed.

(** Обратите внимание на "буллеты", разделяющие доказательства двух
    подцелей. *)

(** Другой пример, с логическими значениями: *)

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity.  Qed.

(** Также у нас могут быть вложенные подцели (и мы будем использовать
    другие "буллеты", чтобы отмечать относящиеся к ним случаи): *)

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.

(** Помимо [-] и [+], в качестве буллета можно использовать [*] (астериск),
    а также любое их повторение (например, [--], [***]).  Также вместо
    использования буллетов мы можем заключать части доказательства в фигурные
    скобки: *)

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
Qed.

(** И последнее: вместо

       intros x y. destruct y as [|y] eqn:E.

   можно писать просто

       intros x [|y].
*)

Theorem plus_1_neq_0' : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.  Qed.

(** Если у конструкторов нет полей, которые нужно называть, можно использовать
    просто [[]], чтобы получить разбор случаев. *)

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.



(* ################################################################# *)
(** * Самопроверка решений *)

(** Вы можете запустить [make BasicsTest.vo], чтобы проверить Ваше решение
    на предмет ряда частых ошибок:

    - Удаление либо переименование упражнений.

    - Изменение утверждения, которое нужно доказать.

    - Незаконченные упражнения. *)

