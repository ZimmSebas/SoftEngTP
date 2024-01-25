% VARIABLES

variables([Registro]).

% TIPOS

def_type(rr,set(tarj)).
def_type(ss,rel(tarj,int)).

% INVARIANTES

% Invariante de Tipos
invariant(registroTarjetasTypeInv).
dec_p_type(registroTarjetasTypeInv(ss)).
registroTarjetasTypeInv(Saldos) :- pfun(Saldos).

% Invariante de Dominio de Registro = Tarjetas
invariant(registroTarjetasDomInv).
dec_p_type(registroTarjetasDomInv(ss,rr)).
registroTarjetasDomInv(Saldos,Registro) :-
    dom(Saldos, Registro).

% ESTADO INICIAL

initial(registroTarjetasInit).
dec_p_type(registroTarjetasInit(ss,rr)).
registroTarjetasInit(Saldos,Registro) :-
    Saldos = {} &
    Registro = {}.


% Dado de alta

dec_p_type(registroOK(ss, ss, rr, rr, tarj)).
registroOK(Saldos, Saldos_, Registro, Registro_, Tarj_i) :-
    Tarj_i nin Registro &
    Registro_ = {Tarj_i / Registro} &
    Saldos_ = {[Tarj_i, 0] / Saldos}.

dec_p_type(tarjetaExistente(ss, ss, rr, rr, tarj)).
tarjetaExistente(Saldos, Saldos_, Registro, Registro_, Tarj_i) :-
    Saldos_ = Saldos &
    Registro_ = Registro &
    Tarj_i in Registro.

operation(registro).
dec_p_type(registro(ss, ss, rr, rr, tarj)).
registro(Saldos, Saldos_, Registro, Registro_, Tarj_i) :-
    registroOK(Saldos, Saldos_, Registro, Registro_, Tarj_i)
    or
    tarjetaExistente(Saldos, Saldos_, Registro, Registro_, Tarj_i).

% Cargar Saldo

dec_p_type(cargarOK(ss, ss, rr, rr, tarj, int)).
cargarOK(Saldos, Saldos_, Registro, Registro_, Tarj_i, Monto_i) :-
    Registro_ = Registro &
    Tarj_i in Registro &
    [Tarj_i,Monto] in Saldos &
    MontoTotal is (Monto+Monto_i) &
    oplus(Saldos, {[Tarj_i, MontoTotal]}, Saldos_).

dec_p_type(tarjetaInexistente(ss, ss, rr, rr, tarj)).
tarjetaInexistente(Saldos, Saldos_, Registro, Registro_, Tarj_i).
    Saldos_ = Saldos &
    Registro_ = Registro &
    Tarj_i nin Registro.

operation(cargar).
dec_p_type(cargar(ss, ss, rr, rr, tarj, int)).
cargar(Saldos, Saldos_, Registro, Registro_, Tarj_i, Monto_i) :-
    cargarOK(Saldos, Saldos_, Registro, Registro_, Tarj_i, Monto_i)
    or
    tarjetaInexistente(Saldos, Saldos_, Registro, Registro_, Tarj_i).


% Pagar

dec_p_type(pagarOK(ss, ss, rr, rr, tarj)).
pagarOK(Saldos, Saldos_, Registro, Registro_, Tarj_i) :-
    Registro_ = Registro &
    Tarj_i in Registro &
    [Tarj_i,Monto] in Saldos &
    Monto >= 100 &
    MontoTotal is (Monto-100) &
    oplus(Saldos, {[Tarj_i, MontoTotal]}, Saldos_).

dec_p_type(saldoInsuficiente(ss, ss, rr, rr, tarj)).
saldoInsuficiente(Saldos, Saldos_, Registro, Registro_, Tarj_i) :-
    Saldos_ = Saldos &
    Registro_ = Registro &
    Tarj_i in Registro &
    [Tarj_i,Monto] in Saldos &
    Monto < 100.

operation(pagar).
dec_p_type(pagar(ss, ss, rr, rr, tarj)).
pagar(Saldos, Saldos_, Registro, Registro_, Tarj_i) :-
    pagarOK(Saldos, Saldos_, Registro, Registro_, Tarj_i)
    or
    tarjetaInexistente(Saldos, Saldos_, Registro, Registro_, Tarj_i)
    or
    saldoInsuficiente(Saldos, Saldos_, Registro, Registro_, Tarj_i).

