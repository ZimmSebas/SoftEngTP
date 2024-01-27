% Verification conditions for registrotarjetas.pl

% Run check_vcs_registrotarjetas to see if the program verifies all the VCs

:- notype_check.

:- consult('registrotarjetas.pl').

:- prolog_call((
    retractall(all_unsat_vc(_,_,_,_,_,_)),
    retractall(dinvariant(_,_,_)),
    retractall(daxiom(_,_,_)),
    (exists_file('registrotarjetas-all.pl') ->
       open('registrotarjetas-all.pl',read,StreamVC)
    ;
       print_notfile('registrotarjetas-all.pl')
    ),
    style_check(-singleton),
    setlog:consult_vc(StreamVC),
    style_check(+singleton),
    close(StreamVC))).

% Change this number for a different timeout (ms)
def_to(60000).

:- prolog_call(nb_setval(vc_num,0)).
:- prolog_call(nb_setval(vc_ok,0)).
:- prolog_call(nb_setval(vc_err,0)).
:- prolog_call(nb_setval(vc_to,0)).
:- prolog_call(nb_setval(vc_time,0)).

:- prolog_call(dynamic(unsat_sol/5)).
:- prolog_call(dynamic(vc_proved/1)).

registroTarjetasInit_sat_registroTarjetasTypeInv :-
  registroTarjetasInit(Saldos,Registro) &
  registroTarjetasTypeInv(Saldos).

registroTarjetasInit_sat_registroTarjetasDomInv :-
  registroTarjetasInit(Saldos,Registro) &
  registroTarjetasDomInv(Saldos,Registro).

registro_is_sat :-
  registro(Saldos,Saldos_,Registro,Registro_,Tarj_i) & 
  delay([Saldos,Registro] neq [Saldos_,Registro_],false).

registro_pi_registroTarjetasTypeInv(Saldos,Saldos,Saldos_,Registro,Registro_,Tarj_i) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    registroTarjetasTypeInv(Saldos) &
    registro(Saldos,Saldos_,Registro,Registro_,Tarj_i) implies
    registroTarjetasTypeInv(Saldos_)
  ).

registro_pi_registroTarjetasDomInv(Saldos,Registro,Saldos,Saldos_,Registro,Registro_,Tarj_i) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    registroTarjetasDomInv(Saldos,Registro) &
    registro(Saldos,Saldos_,Registro,Registro_,Tarj_i) implies
    registroTarjetasDomInv(Saldos_,Registro_)
  ).

cargar_is_sat :-
  cargar(Saldos,Saldos_,Registro,Registro_,Tarj_i,Monto_i) & 
  delay([Saldos,Registro] neq [Saldos_,Registro_],false).

cargar_pi_registroTarjetasTypeInv(Saldos,Saldos,Saldos_,Registro,Registro_,Tarj_i,Monto_i) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    registroTarjetasTypeInv(Saldos) &
    cargar(Saldos,Saldos_,Registro,Registro_,Tarj_i,Monto_i) implies
    registroTarjetasTypeInv(Saldos_)
  ).

cargar_pi_registroTarjetasDomInv(Saldos,Registro,Saldos,Saldos_,Registro,Registro_,Tarj_i,Monto_i) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    registroTarjetasDomInv(Saldos,Registro) &
    cargar(Saldos,Saldos_,Registro,Registro_,Tarj_i,Monto_i) implies
    registroTarjetasDomInv(Saldos_,Registro_)
  ).

pagar_is_sat :-
  pagar(Saldos,Saldos_,Registro,Registro_,Tarj_i) & 
  delay([Saldos,Registro] neq [Saldos_,Registro_],false).

pagar_pi_registroTarjetasTypeInv(Saldos,Saldos,Saldos_,Registro,Registro_,Tarj_i) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    registroTarjetasTypeInv(Saldos) &
    pagar(Saldos,Saldos_,Registro,Registro_,Tarj_i) implies
    registroTarjetasTypeInv(Saldos_)
  ).

pagar_pi_registroTarjetasDomInv(Saldos,Registro,Saldos,Saldos_,Registro,Registro_,Tarj_i) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    registroTarjetasDomInv(Saldos,Registro) &
    pagar(Saldos,Saldos_,Registro,Registro_,Tarj_i) implies
    registroTarjetasDomInv(Saldos_,Registro_)
  ).

update_time(Tf,Ti) :-
  prolog_call(
    (nb_getval(vc_time,VCT),
     VCT_ is VCT + Tf - Ti,
     nb_setval(vc_time,VCT_)
    )
  ).

update_count(C) :-
  prolog_call(
    (nb_getval(C,VCN),
     VCN_ is VCN + 1,
     nb_setval(C,VCN_)
    )
  ).

check_sat_vc(VCID) :-
  prolog_call((setlog:vc_proved(VCID) -> R = proved ; R = unproved)) &
  (R == unproved &
   write('\nChecking ') & write(VCID) & write(' ... ') &
   update_count(vc_num) &
   ((prolog_call(setlog(VCID)) &
    update_count(vc_ok) &
    prolog_call(assertz(vc_proved(VCID))) &
    write_ok)!
    or
    update_count(vc_err) &
    write_err
   )
   or
   R == proved
  ).

check_unsat_vc(VCID) :-
  def_to(TO) &
  prolog_call(
    (VCID =.. [H | _],
     (\+setlog:vc_proved(H) ->
        setlog:all_unsat_vc(H,T,ID,VC,Op,VN),
        write('\nChecking '), write(H), write(' ... '), flush_output,
        setlog(update_count(vc_num)),
        get_time(Ti),
        rsetlog(VC,TO,Cons,Res,[nopfcheck]),
        get_time(Tf)
     ;
        Res = proved
     )
    )
  ) &
  ((Res = failure)! &
    update_count(vc_ok) &
    update_time(Tf,Ti) &
    prolog_call((retractall(setlog:unsat_sol(_,H,_,_,_)),
                 assertz(vc_proved(H)))) &
    write_ok
  or
   (Res = timeout)! &
    update_count(vc_to) &
    write_to
  or
    (Res = proved)!
  or
    update_count(vc_err) &
    % saves the solution to be used by findh
    prolog_call((retractall(setlog:unsat_sol(_,H,_,_,_)),
                 assertz(unsat_sol(T,H,ID,Cons,VN)))) &
    write_err
  ).

write_ok :-
  prolog_call(ansi_format([bold,fg(green)],'OK',[])).

write_to :-
  prolog_call(ansi_format([bold,fg(255,255,50)],'TIMEOUT',[])).

write_err :-
  prolog_call(ansi_format([bold,fg(red)],'ERROR',[])).

check_vcs_registrotarjetas :- prolog_call(setlog(check_aux!)).

check_aux :-
  prolog_call(
    (retractall(unsat_sol(_,_,_,_,_)),
     nb_setval(vc_num,0),
     nb_setval(vc_time,0),
     nb_setval(vc_ok,0),
     nb_setval(vc_err,0),
     nb_setval(vc_to,0)
    )
  ) &
  check_sat_vc(registroTarjetasInit_sat_registroTarjetasTypeInv) &
  check_sat_vc(registroTarjetasInit_sat_registroTarjetasDomInv) &
  check_sat_vc(registro_is_sat) &
  check_sat_vc(cargar_is_sat) &
  check_sat_vc(pagar_is_sat) &
  check_unsat_vc(registro_pi_registroTarjetasTypeInv(Saldos,Saldos,Saldos_,Registro,Registro_,Tarj_i)) &
  check_unsat_vc(registro_pi_registroTarjetasDomInv(Saldos,Registro,Saldos,Saldos_,Registro,Registro_,Tarj_i)) &
  check_unsat_vc(cargar_pi_registroTarjetasTypeInv(Saldos,Saldos,Saldos_,Registro,Registro_,Tarj_i,Monto_i)) &
  check_unsat_vc(cargar_pi_registroTarjetasDomInv(Saldos,Registro,Saldos,Saldos_,Registro,Registro_,Tarj_i,Monto_i)) &
  check_unsat_vc(pagar_pi_registroTarjetasTypeInv(Saldos,Saldos,Saldos_,Registro,Registro_,Tarj_i)) &
  check_unsat_vc(pagar_pi_registroTarjetasDomInv(Saldos,Registro,Saldos,Saldos_,Registro,Registro_,Tarj_i)) &
  prolog_call(
    (nb_getval(vc_num,VCN),
     nb_getval(vc_time,VCT),
     nb_getval(vc_ok,VCOK),
     nb_getval(vc_err,VCE),
     nb_getval(vc_to,VCTO)
    )
  ) &
  nl & nl &
  write("Total VCs: ") & write(VCN) &
  write(" (discharged: ") & write(VCOK) &
  write(", failed: ") & write(VCE) &
  write(", timeout: ") & write(VCTO) & write(")") & nl &
  write("Execution time (discharged): ") & write(VCT) & write(" s").

:- nl & prolog_call(ansi_format([bold,fg(green)],'Type checking has been deactivated.',[])) & nl & nl.

:- nl & prolog_call(ansi_format([bold,fg(green)],'Call check_vcs_registrotarjetas to run the verification conditions.',[])) & nl & nl.

