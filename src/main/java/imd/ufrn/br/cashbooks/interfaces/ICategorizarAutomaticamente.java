package imd.ufrn.br.cashbooks.interfaces;

import imd.ufrn.br.cashbooks.model.Movimentacao;

public interface ICategorizarAutomaticamente {
	
	public /*@ pure @*/ void categorizar(Movimentacao mov);
}
