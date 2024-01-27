% VARIABLES

variables([Registro, Saldos]).

% TIPOS

def_type(rr,set(tarj)).
def_type(ss,rel(tarj,int)).

% INVARIANTES

% Invariante de Tipos
invariant(registroTarjetasTypeInv).
dec_p_type(registroTarjetasTypeInv(ss)).
registroTarjetasTypeInv(Saldos) :- pfun(Saldos).

dec_p_type(n_registroTarjetasTypeInv(ss)).
n_registroTarjetasTypeInv(Saldos) :-
    neg(pfun(Saldos)).

% Invariante de Dominio de Registro = Tarjetas
invariant(registroTarjetasDomInv).
dec_p_type(registroTarjetasDomInv(ss,rr)).
registroTarjetasDomInv(Saldos,Registro) :-
    dom(Saldos, Registro).

dec_p_type(n_registroTarjetasDomInv(ss,rr)).
n_registroTarjetasDomInv(Saldos,Registro) :-
    neg(dom(Saldos, Registro)).

% ESTADO INICIAL

initial(registroTarjetasInit).
dec_p_type(registroTarjetasInit(ss,rr)).
registroTarjetasInit(Saldos,Registro) :-
    Saldos = {} &
    Registro = {}.


% Dado de alta

dec_p_type(registroOK(ss, ss, rr, rr, tarj)).
registroOK(Saldos, Saldos_, Registro, Registro_, Tarj_i) :-
    dom(Saldos, TARJ) &
    Tarj_i nin TARJ &
    Tarj_i nin Registro &
    Registro_ = {Tarj_i / Registro} &
    Saldos_ = {[Tarj_i, 0] / Saldos}.

dec_p_type(tarjetaExistente(ss, ss, rr, rr, tarj)).
tarjetaExistente(Saldos, Registro, Tarj_i) :-
    dom(Saldos, TARJ) &
    Tarj_i in Registro &
    Tarj_i in TARJ.

operation(registro).
dec_p_type(registro(ss, ss, rr, rr, tarj)).
registro(Saldos, Saldos_, Registro, Registro_, Tarj_i) :-
    registroOK(Saldos, Saldos_, Registro, Registro_, Tarj_i)
    or
    tarjetaExistente(Saldos, Registro, Tarj_i) & Saldos_ = Saldos & Registro_ = Registro.

% Cargar saldo

dec_p_type(cargarOK(ss, ss, rr, rr, tarj, int)).
cargarOK(Saldos, Saldos_, Registro, Registro_, Tarj_i, Monto_i) :-
    Registro_ = Registro &
    Tarj_i in Registro &
    dom(Saldos, TARJ) &
    Tarj_i in TARJ &
    [Tarj_i,Monto] in Saldos &
    MontoTotal is (Monto+Monto_i) &
    oplus(Saldos, {[Tarj_i, MontoTotal]}, Saldos_).

dec_p_type(tarjetaInexistente(ss, ss, rr, rr, tarj)).
tarjetaInexistente(Saldos, Registro, Tarj_i).
    dom(Saldos, TARJ) &
    Tarj_i nin Registro &
    Tarj_i nin TARJ.

operation(cargar).
dec_p_type(cargar(ss, ss, rr, rr, tarj, int)).
cargar(Saldos, Saldos_, Registro, Registro_, Tarj_i, Monto_i) :-
    cargarOK(Saldos, Saldos_, Registro, Registro_, Tarj_i, Monto_i)
    or
    tarjetaInexistente(Saldos, Registro, Tarj_i) & Saldos_ = Saldos & Registro_ = Registro.


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
saldoInsuficiente(Saldos, Registro, Tarj_i) :-
    Tarj_i in Registro &
    [Tarj_i,Monto] in Saldos &
    Monto < 100.

operation(pagar).
dec_p_type(pagar(ss, ss, rr, rr, tarj)).
pagar(Saldos, Saldos_, Registro, Registro_, Tarj_i) :-
    pagarOK(Saldos, Saldos_, Registro, Registro_, Tarj_i)
    or
    tarjetaInexistente(Saldos, Registro, Tarj_i) & Saldos_ = Saldos & Registro_ = Registro
    or
    saldoInsuficiente(Saldos, Registro, Tarj_i) & Saldos_ = Saldos & Registro_ = Registro.

