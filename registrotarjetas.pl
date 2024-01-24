axiom(minsaldo).
dec_p_type(minsaldo(int)).
minsaldo() :- 0

axiom(valorviaje).
dec_p_type(valorviaje(int)).
valorviaje() :- 100

% VARIABLES

variables([Registro]).

% TIPOS

def_type(ss,set([tarj,int])).
def_type(rr,set(tarj)).

% INVARIANTES

% Invariante de Tipos
invariant(registroTarjetasTypeInv).
dec_p_type(registroTarjetasTypeInv(ss)).
registroTarjetasTypeInv(Saldos) :- pfun(Saldos).

% Invariante de Dominio de Registro = Tarjetas
invariant(registroTarjetasDomInv).
dec_p_type(registroTarjetasTypeInv(ss,rr)).
registroTarjetasDomInv(Saldos,Registro) :-
    dom(Saldos, TARJ) &
    TARJ == Registro.

% ESTADO INICIAL

initial(registroTarjetasInit).
registroTarjetasInit(Saldos,Registro) :-
    Saldos = {} &
    Registro = {}.


% Dado de alta

dec_p_type(registroOK(ss, ss, rr, rr, tarj)).
registroOK(Saldos, Saldos_, Registro, Registro_, Tarj_i) :-
    dom(Registro, TARJ) &
    Tarj_i nin TARJ &
    Registro_ = {TARJ_i / Registro} &
    Saldos_ = {[TARJ_i, minSaldo] / Saldos}.

dec_p_type(tarjetaExistente(ss, ss, rr, rr, tarj)).
tarjetaExistente(Saldos, Saldos_, Registro, Registro_, Tarj_i) :-
    Saldos_ = Saldos &
    Registro_ = Registro &
    dom(Registro, TARJ) &
    Tarj_i in TARJ.

operation(registro).
dec_p_type(registro(ss, ss, rr, rr, tarj)).
registro(Saldos, Saldos_, Registro, Registro_, Tarj_i) :-
    registroOK(State, State_, Tarj_i)
    or
    tarjetaExistente(State, State_, Tarj_i).

% Cargar Saldo

dec_p_type(cargarOK(ss, ss, rr, rr, tarj, int)).
cargarOK(Saldos, Saldos_, Registro, Registro_, Tarj_i, Monto_i) :-
    Registro_ = Registro &
    dom(Registro, TARJ) &
    Tarj_i in TARJ &
    oplus(Saldos, , Saldos_)

dec_p_type(tarjetaInexistente(ss, ss, rr, rr, tarj, int)).
tarjetaInexistente(Saldos, Saldos_, Registro, Registro_, Tarj_i).
    Saldos_ = Saldos &
    Registro_ = Registro &
    dom(Registro, TARJ) &
    Tarj_i nin TARJ.

operation(cargar).
dec_p_type(cargar(ss, ss, rr, rr, tarj, int)).
cargar(Saldos, Saldos_, Registro, Registro_, Tarj_i) :-
    cargarOK(Saldos, Saldos_, Registro, Registro_, Tarj_i)
    or
    tarjetaInexistente(Saldos, Saldos_, Registro, Registro_, Tarj_i).


% Pagar

dec_p_type(pagarOK(ss, ss, rr, rr, tarj)).
pagarOK(Saldos, Saldos_, Registro, Registro_, Tarj_i) :-
    Registro_ = Registro &
    dom(Registro, TARJ) &
    applyTo(Saldos, Tarj_i, Monto) >= valorViaje &
    oplus(Saldos, [Tarj_i, applyTo(Saldos, Tarj_i, Monto)-valorViaje], Saldos_)

dec_p_type(saldoInsuficiente(ss, ss, rr, rr, tarj)).
saldoInsuficiente(Saldos, Saldos_, Registro, Registro_, Tarj_i) :-
    Saldos_ = Saldos &
    Registro_ = Registro &
    dom(Registro, TARJ) &
    applyTo(Saldos, Tarj_i, Monto) < valorViaje

operation(pagar).
dec_p_type(pagar(ss, ss, rr, rr, tarj)).
pagar(Saldos, Saldos_, Registro, Registro_, Tarj_i) :-
    pagarOK(Saldos, Saldos_, Registro, Registro_, Tarj_i)
    or
    tarjetaInexistente(Saldos, Saldos_, Registro, Registro_, Tarj_i).
    or
    saldoInsuficiente(Saldos, Saldos_, Registro, Registro_, Tarj_i).



















