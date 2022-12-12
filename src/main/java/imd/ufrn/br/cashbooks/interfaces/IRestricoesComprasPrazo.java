package imd.ufrn.br.cashbooks.interfaces;

import java.time.LocalDate;

import imd.ufrn.br.cashbooks.model.Movimentacao;

public interface IRestricoesComprasPrazo {
	
	//@ public model instance int dataLimite;
	//@ public invariant dataLimite == 30;
	
	/*@ ensures \result == mov.getDataMovimentacao().plusDays(dataLimite);@*/
	public /*@ pure @*/ LocalDate calcularDataLimite(Movimentacao mov);
	
	/*@ 	requires mov.getDataCobranca().isAfter(calcularDataLimite(mov));
	  @		ensures \result == false;
	  @ also
	  @		requires mov.getDataCobranca().isBefore(calcularDataLimite(mov));
	  @		ensures \result == true;@*/
	public /*@ pure @*/ boolean validarMovimentacao(Movimentacao mov);
	
	//@ public model instance int limiteCompras;
	//@ public invariant limiteCompras == 3;
	
	/*@ ensures \result == limiteCompras; @*/
	public /*@ pure @*/ int getLimite();
}
