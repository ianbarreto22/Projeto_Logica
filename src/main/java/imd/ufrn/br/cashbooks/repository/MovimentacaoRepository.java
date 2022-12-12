package imd.ufrn.br.cashbooks.repository;

import java.time.LocalDate;
import java.util.List;

import org.springframework.data.jpa.repository.JpaRepository;

import imd.ufrn.br.cashbooks.model.Cliente;
import imd.ufrn.br.cashbooks.model.Movimentacao;

public interface MovimentacaoRepository extends JpaRepository<Movimentacao, Long>{
	List<Movimentacao> findAllByDataMovimentacao(LocalDate dataMovimentacao);
	List<Movimentacao> findAllByDataCobranca(LocalDate dataCobranca);
	List<Movimentacao> findAllByCliente(Cliente cliente);
}
