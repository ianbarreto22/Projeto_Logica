package imd.ufrn.br.cashbooks.repository;

import java.util.Optional;

import org.springframework.data.jpa.repository.JpaRepository;

import imd.ufrn.br.cashbooks.model.Usuario;

public interface UsuarioRepository extends JpaRepository<Usuario, Long>{
	Optional<Usuario> findByEmail(String username);
}
