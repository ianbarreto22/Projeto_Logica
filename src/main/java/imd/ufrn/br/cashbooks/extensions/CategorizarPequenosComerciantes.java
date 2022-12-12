package imd.ufrn.br.cashbooks.extensions;

import imd.ufrn.br.cashbooks.interfaces.ICategorizarAutomaticamente;
import imd.ufrn.br.cashbooks.model.Movimentacao;
import imd.ufrn.br.cashbooks.model.enums.Categoria;

public class CategorizarPequenosComerciantes implements ICategorizarAutomaticamente {
	
	
	/*@ 	requires mov != null;
	@		requires mov.getDescricao() != null;
	@		ensures mov.getCategoria() == Categoria.ROUBO;
	@	also
	@		requires mov != null;
	@		requires mov.getDescricao() != null;
	@		ensures mov.getCategoria() == Categoria.ESTOQUE;
	@	also
	@		requires mov != null;
	@		requires mov.getDescricao() != null;
	@		ensures mov.getCategoria() == Categoria.CAIXA;
	@	also
	@		requires mov != null;
	@		requires mov.getDescricao() != null;
	@		ensures mov.getCategoria() == Categoria.DESPESAS_DIVERSAS;
	@
	@*/
	@Override
	public void categorizar(Movimentacao mov) {
		String descricao = mov.getDescricao().toLowerCase();
		
		if(descricao.contains("roubo") || descricao.contains("furto") || descricao.contains("assalto")) {
			mov.setCategoria(Categoria.ROUBO);
		}//ROUBO
		else if(descricao.contains("estoque") || descricao.contains("carga") || descricao.contains("carregamento") || descricao.contains("quilo") 
				|| descricao.contains("kg") || descricao.contains("reposiçao") || descricao.contains("reposicao") || descricao.contains("reposição") || descricao.contains("reca")) {
			mov.setCategoria(Categoria.ESTOQUE);
		}//ESTOQUE
		else if(descricao.contains("caixa") || descricao.contains("venda") || descricao.contains("compras") || descricao.contains("fiado") ) {
			mov.setCategoria(Categoria.CAIXA);
		}//CAIXA
		else {
			mov.setCategoria(Categoria.DESPESAS_DIVERSAS);
		}//DESPESAS_DIVERSAS
		
	}
}
