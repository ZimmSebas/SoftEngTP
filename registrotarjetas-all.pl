dinvariant(registroTarjetasTypeInv,registroTarjetasTypeInv(Saldos)).
dinvariant(registroTarjetasDomInv,registroTarjetasDomInv(Saldos,Registro)).
all_unsat_vc(registro_pi_registroTarjetasTypeInv,inv,registroTarjetasTypeInv,registro_pi_registroTarjetasTypeInv(Saldos,Saldos,Saldos_,Registro,Registro_,Tarj_i),registro(Saldos,Saldos_,Registro,Registro_,Tarj_i)).
all_unsat_vc(registro_pi_registroTarjetasDomInv,inv,registroTarjetasDomInv,registro_pi_registroTarjetasDomInv(Saldos,Registro,Saldos,Saldos_,Registro,Registro_,Tarj_i),registro(Saldos,Saldos_,Registro,Registro_,Tarj_i)).
all_unsat_vc(cargar_pi_registroTarjetasTypeInv,inv,registroTarjetasTypeInv,cargar_pi_registroTarjetasTypeInv(Saldos,Saldos,Saldos_,Registro,Registro_,Tarj_i,Monto_i),cargar(Saldos,Saldos_,Registro,Registro_,Tarj_i,Monto_i)).
all_unsat_vc(cargar_pi_registroTarjetasDomInv,inv,registroTarjetasDomInv,cargar_pi_registroTarjetasDomInv(Saldos,Registro,Saldos,Saldos_,Registro,Registro_,Tarj_i,Monto_i),cargar(Saldos,Saldos_,Registro,Registro_,Tarj_i,Monto_i)).
all_unsat_vc(pagar_pi_registroTarjetasTypeInv,inv,registroTarjetasTypeInv,pagar_pi_registroTarjetasTypeInv(Saldos,Saldos,Saldos_,Registro,Registro_,Tarj_i),pagar(Saldos,Saldos_,Registro,Registro_,Tarj_i)).
all_unsat_vc(pagar_pi_registroTarjetasDomInv,inv,registroTarjetasDomInv,pagar_pi_registroTarjetasDomInv(Saldos,Registro,Saldos,Saldos_,Registro,Registro_,Tarj_i),pagar(Saldos,Saldos_,Registro,Registro_,Tarj_i)).
