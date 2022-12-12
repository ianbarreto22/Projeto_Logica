package imd.ufrn.br.cashbooks.extensions;

import java.time.format.DateTimeFormatter;
import java.util.List;

import imd.ufrn.br.cashbooks.interfaces.IGerarRelatorio;
import imd.ufrn.br.cashbooks.model.Movimentacao;

public class RelatorioCSV implements IGerarRelatorio {
	
	@Override
	public String gerarRelatorio(List<Movimentacao> movimentacoes) {
		String csvText = "Data,Valor,Cobrança,Tipo,Categoria,Descrição\n"; // Cabçalho
		
		for(int i = 0; i < movimentacoes.size(); i++) {
			csvText += movimentacoes.get(i).getDataMovimentacao().format(DateTimeFormatter.ofPattern("dd/MM/YYYY")) + ',' + 
					"R$ " + String.format("%.2f", movimentacoes.get(i).getValor()) + ',' +
					movimentacoes.get(i).getDataCobranca().format(DateTimeFormatter.ofPattern("dd/MM/YYYY")) + ',' +
					movimentacoes.get(i).getStatus().name() + ',' +
					movimentacoes.get(i).getCategoria().name() + ',' +
					movimentacoes.get(i).getDescricao() + '\n';
		}
		
		return csvText;
	}
	
}
