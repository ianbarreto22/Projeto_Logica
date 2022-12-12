package imd.ufrn.br.cashbooks.repository;

import org.springframework.data.jpa.repository.JpaRepository;
import org.springframework.stereotype.Repository;

import imd.ufrn.br.cashbooks.model.Cliente;

@Repository
public interface ClienteRepository extends JpaRepository<Cliente, Long>{

}
