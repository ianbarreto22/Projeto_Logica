package imd.ufrn.br.cashbooks.extensions;

import java.time.LocalDate;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Component;

import imd.ufrn.br.cashbooks.interfaces.IRestricoesComprasPrazo;
import imd.ufrn.br.cashbooks.model.Movimentacao;
import imd.ufrn.br.cashbooks.service.MovimentacaoService;

@Component
public class RegraPequenosComerciantes implements IRestricoesComprasPrazo {
	
	private static int LIMITE_COMPRAS = 3;//@ in limiteCompras;
	
	//@ public represents LIMITE_COMPRAS = 3;
	//@public represents limiteCompras = LIMITE_COMPRAS;
	
	private static int LIMITE_DIAS = 30; //@ in dataLimite;
	
	//@ public represents LIMITE_DIAS = 30;
	//@ public represents dataLimite = LIMITE_DIAS;
	
	@Autowired 
	MovimentacaoService serviceMovimentacao;

	@Override
	public LocalDate calcularDataLimite(Movimentacao mov) {
		return mov.getDataMovimentacao().plusDays(LIMITE_DIAS);
	}

	@Override
	public boolean validarMovimentacao(Movimentacao mov) {
		
		
		System.out.println(mov.getDataCobranca() + " " + mov.getDataCobranca().isAfter(calcularDataLimite(mov))	);
		if(mov.getDataCobranca().isAfter(calcularDataLimite(mov))) {
			return false;
		}
		
		int count=0;
		
		if(mov.getCliente() != null) {
			for(Movimentacao m : serviceMovimentacao.findAllByCliente(mov.getCliente())) {
				if(!m.isPago()) {
					count++;
				}
			}
			System.out.println(count);
			if(count >= LIMITE_COMPRAS) {
				return false;
			}
		}
		return true;
	}

	@Override
	public int getLimite() {
		return LIMITE_COMPRAS;
	}
}
