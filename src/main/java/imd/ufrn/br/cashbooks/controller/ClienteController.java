package imd.ufrn.br.cashbooks.controller;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Controller;
import org.springframework.ui.Model;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.ModelAttribute;
import org.springframework.web.bind.annotation.PathVariable;
import org.springframework.web.bind.annotation.PostMapping;
import org.springframework.web.bind.annotation.PutMapping;
import org.springframework.web.bind.annotation.RequestBody;
import org.springframework.web.bind.annotation.RequestMapping;

import imd.ufrn.br.cashbooks.model.Cliente;
import imd.ufrn.br.cashbooks.model.Movimentacao;
import imd.ufrn.br.cashbooks.model.Usuario;
import imd.ufrn.br.cashbooks.repository.MovimentacaoRepository;
import imd.ufrn.br.cashbooks.service.ClienteService;
import imd.ufrn.br.cashbooks.service.MovimentacaoService;
import imd.ufrn.br.cashbooks.service.UsuarioService;


@Controller
@RequestMapping("/clientes")
public class ClienteController {
	
	@Autowired 
	private ClienteService serviceCliente;
	
	
	@Autowired
	private MovimentacaoRepository repositoryMovimentacao;
	
	@Autowired
	private MovimentacaoService serviceMovimentacao;
	
	@Autowired
	private UsuarioService serviceUsuario;

	@GetMapping
	public String index(Model model) {
		Usuario proprietario = serviceUsuario.getUsuario();
		
		model.addAttribute("companyName", proprietario.getNomeComercio());
		model.addAttribute("color", proprietario.getCor());
		
		model.addAttribute("listClientes", serviceCliente.findAll());
		
		return "cliente/index";
	}
	
	@GetMapping(value="/new")
	public String create(Model model, @ModelAttribute Cliente entityCliente) {
		Usuario proprietario = serviceUsuario.getUsuario();
		
		model.addAttribute("companyName", proprietario.getNomeComercio());
		model.addAttribute("color", proprietario.getCor());
		
		model.addAttribute("cliente", entityCliente);
		return "cliente/form";
	}
	
	@PostMapping
	public String create(@RequestBody Cliente entityCliente) {
		entityCliente = serviceCliente.insert(entityCliente);
		
		return "redirect:/clientes/";
	}
	
	@GetMapping(value="/edit/{id}")
	public String edit(@PathVariable("id") Long id, Model model) {
		Cliente entityCliente = serviceCliente.findById(id);
		
		Usuario proprietario = serviceUsuario.getUsuario();
		
		model.addAttribute("companyName", proprietario.getNomeComercio());
		model.addAttribute("color", proprietario.getCor());
		
		model.addAttribute("cliente", entityCliente);
		
		return "cliente/form";
	}
	
	@PutMapping
	public String edit(@RequestBody Cliente entityCliente) {
		
		serviceCliente.update(entityCliente.getId(), entityCliente);
		
		return "redirect:/clientes/";
	}
	
	@GetMapping(value="/delete/{id}")
	public String delete(@PathVariable Long id) {
		
		Cliente cliente = serviceCliente.findById(id);
		
		for(Movimentacao mov : repositoryMovimentacao.findAllByCliente(cliente)) {
			serviceMovimentacao.delete(mov.getId());
		}
		
		serviceCliente.delete(id);
		
		return "redirect:/clientes/";
	}
	
	@GetMapping(value="/{id}")
	public String see(@PathVariable Long id, Model model) {
		Cliente entityCliente = serviceCliente.findById(id);
		serviceCliente.calcularDivida(entityCliente);
		
		Usuario proprietario = serviceUsuario.getUsuario();
		
		model.addAttribute("companyName", proprietario.getNomeComercio());
		model.addAttribute("color", proprietario.getCor());
		
		model.addAttribute("cliente", entityCliente);
		model.addAttribute("movimentacoes", serviceMovimentacao.findAllByCliente(entityCliente));
		
		return "cliente/ver-cliente";
	}
}