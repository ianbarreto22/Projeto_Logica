package imd.ufrn.br.cashbooks.interfaces;

import java.util.List;

import imd.ufrn.br.cashbooks.model.Movimentacao;

public interface IGerarRelatorio {
	public abstract String gerarRelatorio(List<Movimentacao> movimentacoes);
}