package imd.ufrn.br.cashbooks.controller;

import java.io.IOException;
import java.io.PrintWriter;

import javax.servlet.http.HttpServletResponse;

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

import imd.ufrn.br.cashbooks.model.Movimentacao;
import imd.ufrn.br.cashbooks.model.Usuario;
import imd.ufrn.br.cashbooks.model.enums.Categoria;
import imd.ufrn.br.cashbooks.model.enums.MovimentacaoStatus;
import imd.ufrn.br.cashbooks.service.ClienteService;
import imd.ufrn.br.cashbooks.service.MovimentacaoService;
import imd.ufrn.br.cashbooks.service.UsuarioService;

@Controller
@RequestMapping("/movimentacoes")
public class MovimentacaoController {

	@Autowired 
	private MovimentacaoService serviceMovimentacao;
	
	@Autowired 
	private ClienteService serviceCliente;
	
	@Autowired UsuarioService serviceUsuario;

	@GetMapping
	public String index(Model model) {
		Usuario proprietario = serviceUsuario.getUsuario();
		
		model.addAttribute("companyName", proprietario.getNomeComercio());
		model.addAttribute("color", proprietario.getCor());
		model.addAttribute("categories", Categoria.values());
		model.addAttribute("statuses", MovimentacaoStatus.values());
		model.addAttribute("balancoDiario", serviceMovimentacao.getBalancoDiario());
		model.addAttribute("listMovimentacoes", serviceMovimentacao.findAll());
		
		return "movimentacao/index";
	}
	
	@GetMapping(value = "print.csv")
	public void print(HttpServletResponse response) throws IOException {

	    response.addHeader("content-type", "text/csv; charset=utf-8");
	    response.setStatus(200);

	    PrintWriter out = response.getWriter();
	    out.println(serviceMovimentacao.getRelatorio());
	}

	@GetMapping(value = "/new")
	public String create(Model model, @ModelAttribute Movimentacao entityMovimentacao) {
//		entityMovimentacao.setProprietario(serviceProprietario.findById(1L));
		
		Usuario proprietario = serviceUsuario.getUsuario();
		
		model.addAttribute("companyName", proprietario.getNomeComercio());
		model.addAttribute("color", proprietario.getCor());
		
		model.addAttribute("statuses", MovimentacaoStatus.values());
		model.addAttribute("categories", Categoria.values());
		model.addAttribute("clientes", serviceCliente.findAll());
		model.addAttribute("movimentacao", entityMovimentacao); //nulo para view reconhecer como create
		
		return "movimentacao/form";
	}
	
	@PostMapping
	public String create(@RequestBody Movimentacao entityMovimentacao) {
		serviceMovimentacao.insert(entityMovimentacao);
		
		return "redirect:/movimentacoes/";
	}
	
	@GetMapping(value = "/edit/{id}")
	public String edit(@PathVariable("id") Long id, Model model) {
		
		Movimentacao entityMovimentacao = serviceMovimentacao.findById(id);
		
		Usuario proprietario = serviceUsuario.getUsuario();
		
		model.addAttribute("companyName", proprietario.getNomeComercio());
		model.addAttribute("color", proprietario.getCor());
		model.addAttribute("categories", Categoria.values());
		model.addAttribute("statuses", MovimentacaoStatus.values());
		model.addAttribute("clientes", serviceCliente.findAll());
		model.addAttribute("movimentacao", entityMovimentacao);
		
		return "movimentacao/form";
	}
	
	@PutMapping
	public String edit(@RequestBody Movimentacao entityMovimentacao) {
		serviceMovimentacao.update(entityMovimentacao.getId(), entityMovimentacao);
		
		return "redirect:/movimentacoes/";
	}
	
	@GetMapping(value = "/delete/{id}")
	public String delete(@PathVariable("id") Long id) {
		
		serviceMovimentacao.delete(id);
		
		return "redirect:/movimentacoes/";
	}
	
	@GetMapping(value = "/{id}")
	public String see(@PathVariable("id") Long id, Model model) {
		
		Usuario proprietario = serviceUsuario.getUsuario();
		
		model.addAttribute("companyName", proprietario.getNomeComercio());
		model.addAttribute("color", proprietario.getCor());
		
		Movimentacao entityMovimentacao = serviceMovimentacao.findById(id);
		
		model.addAttribute("movimentacao", entityMovimentacao);
		
		return "movimentacao/ver-movimentacao";
	}
}