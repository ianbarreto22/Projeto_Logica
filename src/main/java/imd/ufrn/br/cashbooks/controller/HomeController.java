package imd.ufrn.br.cashbooks.controller;

import javax.servlet.http.HttpServletRequest;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Controller;
import org.springframework.ui.Model;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.PathVariable;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RequestMethod;

import imd.ufrn.br.cashbooks.model.Usuario;
import imd.ufrn.br.cashbooks.service.ClienteService;
import imd.ufrn.br.cashbooks.service.MovimentacaoService;
import imd.ufrn.br.cashbooks.service.UsuarioService;

@Controller
public class HomeController {
	
	@Autowired 
	private MovimentacaoService serviceMovimentacao;
	
	@Autowired 
	private ClienteService serviceCliente;
	
	@Autowired
	private UsuarioService serviceUsuario;

	@RequestMapping(value = "/", method = RequestMethod.GET)
	public String home(HttpServletRequest request, Model model) {
		
		//testando passar valores para a view (remover depois, é só um teste)
//		String test = request.getParameter("test"); // pegar parametro (imagino q funciona para POST também)
//		if(test == null) test = "Campo GET ?test= veio nulo!";
		
		// conteúdo dentro do UI Model para ser puxado na página.
		Usuario usuario = serviceUsuario.getUsuario();
		
		model.addAttribute("companyName", usuario.getNomeComercio());
		model.addAttribute("color", usuario.getCor());
		model.addAttribute("proprietario", usuario);
		
		model.addAttribute("balancosRecentes", serviceMovimentacao.getBalancoRetroativamente(30));
		model.addAttribute("movimentacoesFiado", serviceMovimentacao.getMovimentacoesFiadoHoje());
  		model.addAttribute("clientesDevendo", serviceCliente.getClientesDevendo());
				
		return "home/index";
	}
	
	@GetMapping(value="/clientes-devendo")
	public String listarClientesDevendo(Model model) {
		
		Usuario usuario = serviceUsuario.getUsuario();
		
		model.addAttribute("companyName", usuario.getNomeComercio());
		model.addAttribute("color", usuario.getCor());
		
		model.addAttribute("clientes", serviceCliente.getClientesDevendo());
		
		return "home/clientes-devendo";
	}
	
	@GetMapping(value="/movimentacoes-fiado")
	public String listarMovimentacoesFiado(Model model) {
		Usuario usuario = serviceUsuario.getUsuario();
		
		model.addAttribute("companyName", usuario.getNomeComercio());
		model.addAttribute("color", usuario.getCor());
		
		model.addAttribute("movimentacoes", serviceMovimentacao.getMovimentacoesFiado());
		model.addAttribute("clientes", serviceCliente.getClientesDevendo());
		
		return "home/movimentacoes-fiado";
	}
	
	@GetMapping(value="/movimentacoes-fiado/pagar/{id}")
	public String pagarMovimentacoesFiado(@PathVariable("id") Long id) {
		serviceMovimentacao.pagarMovimentacao(id);
		
		return "redirect:/movimentacoes-fiado/";
	}
}