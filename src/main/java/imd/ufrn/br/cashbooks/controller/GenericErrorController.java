package imd.ufrn.br.cashbooks.controller;

import javax.servlet.RequestDispatcher;
import javax.servlet.http.HttpServletRequest;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.web.servlet.error.ErrorController;
import org.springframework.http.HttpStatus;
import org.springframework.stereotype.Controller;
import org.springframework.ui.Model;
import org.springframework.web.bind.annotation.RequestMapping;

import imd.ufrn.br.cashbooks.model.Usuario;
import imd.ufrn.br.cashbooks.service.UsuarioService;

@Controller
public class GenericErrorController implements ErrorController {
	
	@Autowired
	private UsuarioService serviceUsuario;

    @RequestMapping("/error")
    public String handleError(HttpServletRequest request, Model model) {
    	Object status = request.getAttribute(RequestDispatcher.ERROR_STATUS_CODE);
    	
    	Usuario proprietario = serviceUsuario.getUsuario();
		
		model.addAttribute("companyName", proprietario.getNomeComercio());
		model.addAttribute("color", proprietario.getCor());
    	
	    Integer statusCode = (status != null) ? Integer.valueOf(status.toString()) : -1;
	    
        if(statusCode == HttpStatus.NOT_FOUND.value()) {
        	model.addAttribute("errorMessage", "Página não encontrada");
        	model.addAttribute("errorDescription", "A página requisitada não pôde ser encontrada.");
        } else if(statusCode == HttpStatus.INTERNAL_SERVER_ERROR.value()) {
        	model.addAttribute("errorMessage", "Erro do servidor!");
        	model.addAttribute("errorDescription", "Algo quebrou internamente no servidor. Tente novamente mais tarde.");
        } else if(statusCode == HttpStatus.UNPROCESSABLE_ENTITY.value()) {
        	model.addAttribute("errorMessage", "Formulário errado!");
        	model.addAttribute("errorDescription", "Algum campo do formulário estava vazio ou não estava válido.");
        } else {
        	model.addAttribute("errorMessage", "Erro de requisição");
        	model.addAttribute("errorDescription", "Algo inesperado ocorreu. Tente novamente mais tarde.");
        }
        return "error/index";
    }
}