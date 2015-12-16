# STAT4290 Final Project
# Patrick Rogan, Qitong Liu, Shuni Fang, Xuyan Xiao
#
# Note, a portion of this code is a modified version of code made by the authors of
# Statistics and Data Analysis for Financial Engineering and presented on Pages 297 - 299,
# specifically the calculation of tangency portfolios by the Markowitz approach.

library(quadprog)
library(quantmod)
library(corrplot)
library(boot)
library(ggplot2)
library(copula)  #  for copula functions
library(fCopulae)  # additional copula functions

# Read in Risk Free Data: Treasury bills (secondary market): 4-week
wd = getwd()
riskFree = read.csv(paste0(wd,'/FRB_H15.csv'),
                    stringsAsFactors=FALSE)
riskFree = riskFree[c(-5:-1),] # remove header information
riskFree[,1] = as.Date(riskFree[,1])
startDateTest = "2009-11-02"
startDate = "2010-11-01"
stopDate = "2015-11-26"
startIX = which(riskFree[,1] == startDateTest)  
stopIX = which(riskFree[,1] == stopDate)  
riskFree = riskFree[c(startIX:stopIX),] #set date range
riskFree[,2] = as.double(riskFree[,2])

# Company Descriptions 
#Berkshire Hathaway Large Investments
symbols = c("AXP","IBM","KO","MCO","WFC","DVA","PG","USB","WMT")

# Get Stock Market Data ---------------------------------------------------
#use S&P500 for market portfolio for CAPM
marketP = getSymbols("^GSPC", from=startDateTest, to=stopDate, src="yahoo",auto.assign = FALSE) 
marketP2 = as.numeric(monthlyReturn(marketP[,6]))
n = length(marketP2)[1] 

mufreeV_full = array(0,c(n)) # 0% interest
RM = 100*marketP2 # monthly market return in percent 
#100*(marketP2[2:n]/marketP2[1:(n-1)] - 1)  #Average daily market returns in percent
marketIX = index(marketP[c(-1,-1*(n+1)),])
for (i in 1:length(mufreeV_full)){ # get risk free daily returns and align with the asset data 
  ix = which(riskFree[,1] == marketIX[i])
  if (is.na(riskFree[i,2])){ # if there is no rate, substitute the rate from the day before
    riskFree[i,2] = riskFree[i-1,2]
  }
  mufreeV_full[i] = riskFree[i,2]/12 #monthly risk free return
}

# If the applicable returns have been saved off, load the file, if not, scrape the whole
# list from yahoo finance and save it off
get_data <- function(symbols, startDateTest, stopDate){

  R_full = try(read.csv(paste0(wd,"/Portfolio_Monthly_Returns.csv")))
  
  if (typeof(R_full) != "character"){
    R_full2 <- R_full[,-1]
    rownames(R_full2) <- R_full[,1]
    return(R_full2)
  }
  else{
    assign(symbols[1], getSymbols(symbols[1], from=startDateTest, to=stopDate,
                                  src="yahoo",auto.assign = FALSE))
    
    R_full = cbind(monthlyReturn(get(symbols[1])[,6]))

    for (symbol in symbols[2:length(symbols)]){
      assign(symbol, 
             getSymbols(symbol, from=startDateTest, to = stopDate, src="yahoo",auto.assign = FALSE))
      assign(paste0(symbol,".a"), 
             adjustOHLC(get(symbol), symbol.name=symbol))
      assign(paste0(symbol,".uA"), 
             adjustOHLC(get(symbol), symbol.name=symbol, use.Adjusted=TRUE)) #get(symbol, pos=.GlobalEnv)
      R_full = cbind(R_full,monthlyReturn(get(paste0(symbol,".uA"))[,6]))
    }
    colnames(R_full) <- symbols
    write.csv(as.data.frame(R_full),"Portfolio_Monthly_Returns.csv",
              row.names = TRUE)
    return(R_full)
  }
}

R_full = get_data(symbols, startDateTest, stopDate) 
means = apply(R_full,2,mean)

# Analysis ----------------------------------------------------------------
mufreeV = mufreeV_full[c(14:dim(R_full)[1])]  ###### These need to be fixed to be the actual stocks selected
R = R_full[c(14:dim(R_full)[1]),]
symbols = colnames(R_full[,])

R = 100*matrix(as.numeric(unlist(R)),nrow=nrow(R)) # Monthly Returns in percent
colnames(R) = symbols
#100*(prices[2:n,]/prices[1:(n-1),] - 1) #Average daily returns in percent
mean_vect = apply(R,2,mean)
cov_mat = cov(R)
sd_vect = sqrt(diag(cov_mat))

# set the constraints matrix based on the number of stocks
Amat = cbind(rep(1,length(symbols)),mean_vect, diag(1,nrow=length(symbols)),diag(-1,nrow=length(symbols)))  

#set the constraints matrix based on the number of stocks, no shorts allowed
Amat_noS = cbind(rep(1,length(symbols)),mean_vect,diag(1,nrow=length(symbols)))  

muP = seq(0.0,1.75,length=200)

# set of 200 possible target values, note these are in %/day,
# allow to vary between min and max mean returns
muP_noS = seq(min(mean_vect)+0.001, max(mean_vect)-0.001,length=200) 

sdP = muP # set up storage for standard deviations of portfolio returns
weights = matrix(0,nrow=200,ncol=length(symbols)) # storage for portfolio weights

sdP_noS = muP # set up storage for standard deviations of portfolio returns, no shorts
weights_noS = matrix(0,nrow=200,ncol=length(symbols)) # storage for portfolio weights, no shorts

for (i in 1:length(muP))  # find the optimal portfolios for each target expected return
{
  #Short selling allowed
  bvec = c(1, muP[i], -0.1*rep(1,length(symbols)),0.8*rep(-1,length(symbols))) # constraint vector
  result = 
    solve.QP(Dmat=2*cov_mat,dvec=rep(0,length(symbols)),Amat=Amat,bvec=bvec,meq=2) 
  sdP[i] = sqrt(result$value)
  weights[i,] = result$solution
  
  #No Shorts
  bvec_noS = c(1, muP_noS[i],rep(0,length(symbols))) 
  # constraint vector, weights unconstrained, no shorts
  result_noS = 
    solve.QP(Dmat=2*cov_mat,dvec=rep(0,length(symbols)),Amat=Amat_noS,bvec=bvec_noS,meq=2) 
  sdP_noS[i] = sqrt(result_noS$value)
  weights_noS[i,] = result_noS$solution
}
mufree = mean(mufreeV) # input value of risk-free interest rate, 

########################## With Short Selling #############################
sharpe =(muP-mufree)/sdP # compute Sharpe ratios
ind = (sharpe == max(sharpe)) # Find maximum Sharpe ratio
options(digits=3)
weights[ind,] # Find tangency portfolio
ind2 = (sdP == min(sdP)) # find the minimum variance portfolio

########################### WO Short Selling ##############################
sharpe_noS = (muP_noS - mufree)/sdP_noS
ind_noS = (sharpe_noS == max(sharpe_noS))
options(digits=3)
weights_noS[ind_noS,] # Find tangency portfolio
ind2_noS = (sdP_noS == min(sdP_noS)) # find the minimum variance portfolio

# Asset Sharpe Ratios
assetSharpes =(mean_vect-mufree)/sqrt(apply(R,2,var)) # compute Sharpe ratios
annualizedAssetSharpes = (mean_vect*12-mufree*12)/(sqrt(apply(R,2,var))*sqrt(12))

# Portfolio Theory --------------------------------------------------------
########################### WO Short Selling ##############################
# Minimum Variance Portfolio
print(cat("Minimum Variance Portfolio Weights wo/SS:",weights_noS[ind2_noS,]))
expectedMonthlyReturn_MV_noS = t(weights_noS[ind2_noS,]) %*% mean_vect
expectedYearlyReturn_MV_noS = expectedMonthlyReturn_MV_noS*12
expectedYearlyRisk_MV_noS = sdP_noS[ind2_noS]*sqrt(12)
SharpeYearly_MV_noS = (expectedYearlyReturn_MV_noS - mufree*12)/expectedYearlyRisk_MV_noS

print(cat("Tangency Portfolio Weights wo/SS:",weights_noS[ind_noS,]))
expectedMonthlyReturn_noS = t(weights_noS[ind_noS,]) %*% mean_vect
expectedYearlyReturn_noS = expectedMonthlyReturn_noS*12
expectedYearlyRisk_noS = sdP[ind_noS]*sqrt(12) # Portfolio Risk
SharpeYearly_noS = (expectedYearlyReturn_noS - mufree*12)/expectedYearlyRisk_noS

########################## With Short Selling #############################
# Minimum Variance Portfolio
print(cat("Minimum Variance Portfolio Weights w/SS:",weights[ind2,]))
expectedMonthlyReturn_MV = t(weights[ind2,]) %*% mean_vect
expectedYearlyReturn_MV = expectedMonthlyReturn_MV*12  
expectedYearlyRisk_MV = sdP[ind2]*sqrt(12)
SharpeYearly_MV = (expectedYearlyReturn_MV - mufree*12)/expectedYearlyRisk_MV

print(cat("Tangency Portfolio Weights w/SS:",weights[ind,]))
expectedMonthlyReturn = t(weights[ind,]) %*% mean_vect
expectedYearlyReturn =expectedMonthlyReturn*12
expectedYearlyRisk = sdP[ind]*sqrt(12) # Portfolio Risk
SharpeYearly = (expectedYearlyReturn - mufree*12)/expectedYearlyRisk

############################ Portfolio Stats #############################
ALLWEIGHTS = data.frame(SYM = symbols, MV_NOS = weights_noS[ind2_noS,]*100, MV = weights[ind2,]*100,
                        T_NOS = weights_noS[ind_noS,]*100, T = weights[ind,]*100)
# Min Var No S, Min Var, Tangency No S, Tangency
keyStatsAnnualized = c("Return", "Risk", "sigma^2","Sharpe Ratio")
pReturns = c(expectedYearlyReturn_MV_noS,expectedYearlyReturn_MV,
             expectedYearlyReturn_noS,expectedYearlyReturn)
pRisks = c(expectedYearlyRisk_MV_noS,expectedYearlyRisk_MV,
           expectedYearlyRisk_noS,expectedYearlyRisk)
pVars = pRisks^2 
pSharpes =c(SharpeYearly_MV_noS,SharpeYearly_MV,SharpeYearly_noS,SharpeYearly)

ANNUALIZEDSTATS = t(data.frame(returns = pReturns,
                             risks = pRisks, vars = pVars, sharpes = pSharpes))
rownames(ANNUALIZEDSTATS) = keyStatsAnnualized

# Asset Allocation --------------------------------------------------------
########################### WO Short Selling ##############################
# Calculate which efficient portfolio gives a 1.0% monthly return (0.5% monthly
# return is on the inefficient fronteer and will not be calculated)
ixx = which(abs(weights_noS%*%mean_vect - 1.0) == min(abs(weights_noS%*%mean_vect - 1.0)))
weights_ixx = weights_noS[ixx,]
sdP_ixx = sdP_noS[ixx]

ERP = 1.0 #Desired % monthly return as specified 
wP_noS = (ERP - mufree)/(expectedMonthlyReturn_noS - mufree)
weights_T6 = wP_noS*weights_noS[ind_noS,] # Asset weights
sdP_T6 = wP_noS*sdP_noS[ind_noS] # Monthly Risk

# efficient then tangency
ASSETWEIGHTS = data.frame(w_eff = c(0,weights_ixx)*100, 
                          w_tan = c((1-wP_noS),weights_T6)*100)

rownames(ASSETWEIGHTS) = c("Risk Free",symbols)

# Add 5% VaR and ES
PORTFOLIORISKS = t(data.frame(risk = c(sdP_ixx,sdP_T6), 
                              var = c("TBD", "TBD"),es = c("TBD", "TBD")))
rownames(PORTFOLIORISKS) = c("Risk", "5% VaR", "ES")  

#################### Plot Tangency With Short Selling ######################
png("Tangency.png",width=583,height=486, units = "px")  #preserve w*h 6*5 ratio
# the efficient frontier (and inefficient frontier)
ind3 = (muP > muP[ind2])
ind4 = (muP < muP[ind2])
IEFFP = data.frame(SDP = sdP[ind4], MUP = muP[ind4]) 
EFFP = data.frame(SDP = sdP[ind3], MUP = muP[ind3])
POS = data.frame(SD = sd_vect,ME = mean_vect,SY = symbols)
EFFL = data.frame(X = c(0,6),Y = mufree+c(0,6)*(muP[ind]-mufree)/sdP[ind])
PS1 = data.frame(X= 0,Y = mufree) # Risk Free
PS2 = data.frame(X = sdP[ind], Y = muP[ind])# show tangency portfolio
PS3 = data.frame(X = sdP[ind2], Y = muP[ind2]) # show minimum variance portfolio

ggplot() + geom_line(data = EFFP, aes(x=SDP,y=MUP), lwd=2) + 
  geom_line(data = IEFFP,aes(x=SDP,y=MUP), lty=2) +
  geom_line(data = EFFL,aes(x=X,y=Y), lwd=2,lty=2) + 
  geom_point(data = PS1, aes(x=X,y=Y), cex=8,pch=16) + 
  geom_point(data = PS2, aes(x=X,y=Y), cex=20,pch="*") + 
  geom_point(data = PS3, aes(x=X,y=Y), cex=15,pch="+") + 
  annotate("text", x= POS$SD, y = POS$ME, size = 6,label = POS$SY) +
  ggtitle("Return vs Risk: Short Selling Allowed") +
  theme(plot.title = element_text(size = rel(2))) +
  labs(x = expression(sigma["P"]),y = expression(mu["P"])) +
  theme(axis.title.x = element_text(size = rel(1.5))) +
  theme(axis.title.y = element_text(size = rel(1.5))) 
graphics.off()

###################### Plot Tangency WO Short Selling ######################
png("Tangency_NOS.png",width=583,height=486, units = "px")  #preserve w*h 6*5 ratio
# the efficient frontier (and inefficient frontier)
ind3_noS = (muP_noS > muP_noS[ind2_noS])
ind4_noS = (muP_noS < muP_noS[ind2_noS])
IEFFPN = data.frame(SDP = sdP_noS[ind4_noS], MUP = muP_noS[ind4_noS]) 
EFFPN = data.frame(SDP = sdP_noS[ind3_noS], MUP = muP_noS[ind3_noS])
POSN = data.frame(SD = sd_vect,ME = mean_vect,SY = symbols)
EFFLN = data.frame(X = c(0,6),Y = mufree+c(0,6)*(muP_noS[ind_noS]-mufree)/sdP_noS[ind_noS])
PS1N = data.frame(X= 0,Y = mufree) # Risk Free
PS2N = data.frame(X = sdP_noS[ind_noS], Y = muP_noS[ind_noS])# show tangency portfolio
PS3N = data.frame(X = sdP_noS[ind2_noS], Y = muP_noS[ind2_noS]) # show minimum variance portfolio
PS4N = data.frame(X = sdP_ixx, Y = 1) #efficient portfolio gives a 1.0% monthly return
PS5N = data.frame(X = sdP_T6, Y = 1) #tangency and risk free portfolio gives a 1.0% monthly return

ggplot() + geom_line(data = EFFPN, aes(x=SDP,y=MUP), lwd=2)  +
  geom_line(data = IEFFPN,aes(x=SDP,y=MUP), lty=2) +
  geom_line(data = EFFLN,aes(x=X,y=Y), lwd=2,lty=2) + 
  geom_point(data = PS1N, aes(x=X,y=Y), cex=8,pch=16) + 
  geom_point(data = PS2N, aes(x=X,y=Y), cex=20,pch="*") + 
  geom_point(data = PS3N, aes(x=X,y=Y), cex=15,pch="+") + 
  geom_point(data = PS4N, aes(x=X,y=Y), cex=12,pch="o") + 
  geom_point(data = PS5N, aes(x=X,y=Y), cex=7,pch=15) + 
  annotate("text", x= POS$SD, y = POS$ME, size = 6,label = POS$SY) +
  ggtitle("Return vs Risk: Short Selling Not Allowed") +
  theme(plot.title = element_text(size = rel(2))) +
  labs(x = expression(sigma["P"]),y = expression(mu["P"])) +
  theme(axis.title.x = element_text(size = rel(1.5))) +
  theme(axis.title.y = element_text(size = rel(1.5))) 
graphics.off()

# CAPM --------------------------------------------------------------------
R_j_t_star=array(0,c(dim(R_full)[1]-13,length(symbols)))

for (i in 1:length(symbols)){
  R_j_t_star[,i] = cbind(R[,i] - mufreeV)
}

R_M_t_star = cbind(RM[c(14:dim(R_full)[1])] - mufreeV)

betas = rep(0,length(symbols))
alphas = rep(0,length(symbols))  
rmM = apply(R_M_t_star,2,mean)

for (j in 1:length(symbols)){
  fitLm1 = lm(formula = R_j_t_star[,j] ~ R_M_t_star)
  alphas[j] = fitLm1$coefficients[[1]] #intercept
  betas[j] = fitLm1$coefficients[[2]] #slope
  print(confint(fitLm1)) #95% CI for beta values calculated 
  if (coef(summary(fitLm1))[1,"Pr(>|t|)"] < 0.05){
    print(cat("Caution!!!! ",symbols[j]," may not follow CAPM!"))
  }
}
rp_vect = (mean_vect - mufree)

png("Risk_Premium_vs_Beta.png",width=583,height=486, units = "px") 
RPDf = data.frame(Beta = betas, R_Premium = rp_vect)
linDF = data.frame(x = seq(0,1.5,0.1), SML = rmM*seq(0,1.5,0.1), VX = rep(1,16),VY=c(seq(1,7, length.out = 16)))
ggplot(data = linDF, aes(x=x,y=SML)) + geom_line() + 
  geom_vline(xintercept = 1, lty = 5) + 
  annotate("text", x= RPDf$Beta,y=RPDf$R_Premium, size = 6,label = symbols) + 
  ggtitle(expression(paste("Risk Premium vs ",beta))) + 
  theme(plot.title = element_text(size = rel(2))) +
  labs(x = expression(beta), y = "Risk Premium") +
  theme(axis.title.x = element_text(size = rel(1.5))) +
  theme(axis.title.y = element_text(size = rel(1.5))) 
dev.off()

BASIC = data.frame(beta = betas)
rownames(BASIC) = c(symbols)

# VaR ---------------------------------------------------------------------
# Parametric and Non-parametric Value At Risk calculations using resampling 
# techniques. VaR calculations are made on the individual assets and then multiplied
# by the weights assigned to the tangency portfolio 

var_hat_np = rep(0,length(symbols)) #in percent for each asset, accounts for shorting
es_hat_np = rep(0,length(symbols)) 
var_hat_p = rep(0,length(symbols)) 
es_hat_p = rep(0,length(symbols)) 

for (i in 1:dim(R)[2]){ 
    S = 100000 #sign(weights[ind,][i])*weights[ind,][i]
    
    #Non-Parametric
    var_hat_np[i] = -S*unname(quantile(R[,i]/100,0.05))
    es_hat_np[i] = -S*sum(R[R[,i] < unname(quantile(R[,i],0.05)),i]/100)/
      sum(R[,i] < unname(quantile(R[,i],0.05)))
    
    #Parametric Normal
    var_hat_p[i] = -S*qnorm(0.05,mean = mean_vect[i],sd = sd_vect[i])/100
    es_hat_p[i] = S*(-1*mean_vect[i] + sd_vect[i]*(dnorm(qnorm(0.05))/0.05))/100
}

var_hat_boot <- function(data,indices){ #Non-Parametric VaR
  d <- data[indices]
  var_hat = unname(quantile(d,0.05))
  return(var_hat)
}

es_hat_boot <- function(data,indices){ #Non-Parametric ES
  d <- data[indices]
  es_hat = sum(d[d < unname(quantile(d,0.05))])/
    sum(d <= unname(quantile(d,0.05)))
  return(es_hat)
}

var_hat_p_boot <- function(data,indices){ #Parametric VaR
  d <- data[indices]
  var_hat = qnorm(0.05,mean <- mean(d),sd <- sd(d))
  return(var_hat)
}

es_hat_p_boot <- function(data,indices){ #Parametric ES
  d <- data[indices]
  es_hat = -1*mean(d) + sd(d)*(dnorm(qnorm(0.05))/0.05)
  return(es_hat)
}

#Non-Parametric
var_hat_boot_low = rep(0,length(symbols)) #set up space
var_hat_boot_high = rep(0,length(symbols)) 
var_hat_se = rep(0,length(symbols)) 
var_hat_bias = rep(0,length(symbols)) 
es_hat_boot_low = rep(0,length(symbols)) 
es_hat_boot_high = rep(0,length(symbols)) 
es_hat_se = rep(0,length(symbols)) 
es_hat_bias = rep(0,length(symbols)) 

#Parametric
var_hat_p_boot_low = rep(0,length(symbols)) #set up space
var_hat_p_boot_high = rep(0,length(symbols)) 
var_hat_p_se = rep(0,length(symbols)) 
var_hat_p_bias = rep(0,length(symbols)) 
es_hat_p_boot_low = rep(0,length(symbols)) 
es_hat_p_boot_high = rep(0,length(symbols)) 
es_hat_p_se = rep(0,length(symbols)) 
es_hat_p_bias = rep(0,length(symbols)) 

for (i in 1:dim(R)[2]){
  S <- 100000 #sign(weights[ind,][i])*weights[ind,][i]
  #plot(results) diagnostic plot
  
  #VaR Non-Parametric
  results <- boot(data = R[,i]/100, statistic = var_hat_boot, R = 2000)
  var_hat_boot_low[i] = -S*boot.ci(results, type="bca")[[4]][5]   
  var_hat_boot_high[i] = -S*boot.ci(results, type="bca")[[4]][4] 
  var_hat_bias[i] = mean(results$t)-results$t0 
  var_hat_se[i] = sd(results$t)
  
  #ES Non-Parametric
  results2 <- boot(data = R[,i]/100, statistic = es_hat_boot, R = 2000)
  es_hat_boot_low[i] = -S*boot.ci(results2, type="bca")[[4]][5]   
  es_hat_boot_high[i] =-S*boot.ci(results2, type="bca")[[4]][4] 
  es_hat_bias[i] = mean(results2$t)-results2$t0 
  es_hat_se[i] = sd(results2$t)
  
  #VaR Parametric
  resultsp <- boot(data = R[,i]/100, statistic = var_hat_p_boot, R = 2000)
  var_hat_p_boot_low[i] = -S*boot.ci(resultsp, type="bca")[[4]][5]   
  var_hat_p_boot_high[i] = -S*boot.ci(resultsp, type="bca")[[4]][4] 
  options(digits = 3)
  var_hat_p_bias[i] = mean(resultsp$t)-resultsp$t0 
  options(digits = 3)
  var_hat_p_se[i] = sd(resultsp$t)
  
  #ES Parametric
  resultsp2 <- boot(data = R[,i]/100, statistic = es_hat_p_boot, R = 2000)
  es_hat_p_boot_low[i] = S*boot.ci(resultsp2, type="bca")[[4]][4] 
  es_hat_p_boot_high[i] =S*boot.ci(resultsp2, type="bca")[[4]][5] 
  options(digits = 3)
  es_hat_p_bias[i] = mean(resultsp2$t)-resultsp2$t0 
  es_hat_p_se[i] = sd(resultsp2$t)
}

# Non-Parametric
boot_var_hat = data.frame(var_hat_np,var_hat_boot_low,var_hat_boot_high,var_hat_bias,
                          var_hat_se)
colnames(boot_var_hat) <- c("VaR_NP","Lower 95% CI", "Upper 95% CI","Bias","SE")
row.names(boot_var_hat) <- symbols

boot_es_hat = data.frame(es_hat_np,es_hat_boot_low,es_hat_boot_high,es_hat_bias,
                         es_hat_se)
colnames(boot_es_hat) <- c("ES_NP","Lower 95% CI", "Upper 95% CI","Bias","SE")
row.names(boot_es_hat) <- symbols

# Parametric Normal
boot_var_p_hat = data.frame(var_hat_p,var_hat_p_boot_low,var_hat_p_boot_high,var_hat_p_bias,
                          var_hat_p_se)
colnames(boot_var_p_hat) <- c("VaR_NP","Lower 95% CI", "Upper 95% CI","Bias","SE")
row.names(boot_var_p_hat) <- symbols

boot_es_p_hat = data.frame(es_hat_p,es_hat_p_boot_low,es_hat_p_boot_high,es_hat_p_bias,
                         es_hat_p_se)
colnames(boot_es_p_hat) <- c("ES_NP","Lower 95% CI", "Upper 95% CI","Bias","SE")
row.names(boot_es_p_hat) <- symbols

# Copula Based VaR and ES -------------------------------------------------
# The best fitting copula was the t-copula with 21.613 degrees of freedom, following the 
# analysis on p 516 of the text:
S = 100000

# Min Variance, no shorts -------------------------------------------------
lambda_p_MV_noS = sqrt((21.613-2)/21.613)*expectedYearlyRisk_MV_noS/sqrt(12)/100
portfolio_var_hat_MV_noS = -S*(expectedMonthlyReturn_MV_noS/100 + lambda_p_MV_noS*qt(0.05,21.613))
portfolio_es_hat_MV_noS = S*(-expectedMonthlyReturn_MV_noS/100 + lambda_p_MV_noS*(
  (dt(qt(0.05,21.613),21.613)/0.05)*((21.613+(qt(0.05,21.613))^2)/(21.613-1))
))

# Min Variance ------------------------------------------------------------
lambda_p_MV = sqrt((21.613-2)/21.613)*expectedYearlyRisk_MV/sqrt(12)/100
portfolio_var_hat_MV = -S*(expectedMonthlyReturn_MV/100 + lambda_p_MV*qt(0.05,21.613))
portfolio_es_hat_MV = S*(-expectedMonthlyReturn_MV/100 + lambda_p_MV*(
  (dt(qt(0.05,21.613),21.613)/0.05)*((21.613+(qt(0.05,21.613))^2)/(21.613-1))
))

# Tangency no shorts ------------------------------------------------------
lambda_p_noS = sqrt((21.613-2)/21.613)*expectedYearlyRisk_noS/sqrt(12)/100
portfolio_var_hat_noS = -S*(expectedMonthlyReturn_noS/100 + lambda_p_noS*qt(0.05,21.613)) 
portfolio_es_hat_noS = S*(-expectedMonthlyReturn_noS/100 + lambda_p_noS*(
  (dt(qt(0.05,21.613),21.613)/0.05)*((21.613+(qt(0.05,21.613))^2)/(21.613-1))
))

# Tangency ----------------------------------------------------------------
lambda_p = sqrt((21.613-2)/21.613)*expectedYearlyRisk/sqrt(12)/100
portfolio_var_hat = -S*(expectedMonthlyReturn/100 + lambda_p*qt(0.05,21.613)) 
portfolio_es_hat = S*(-expectedMonthlyReturn/100 + lambda_p*(
  (dt(qt(0.05,21.613),21.613)/0.05)*((21.613+(qt(0.05,21.613))^2)/(21.613-1))
))

# Efficient Portfolio -----------------------------------------------------
lambda_e = sqrt((21.613-2)/21.613)*sdP_ixx/100
portfolio_var_hat_e = -S*(1/100 + lambda_e*qt(0.05,21.613))  
portfolio_es_hat_e = S*(-1/100 + lambda_e*(
  (dt(qt(0.05,21.613),21.613)/0.05)*((21.613+(qt(0.05,21.613))^2)/(21.613-1))
))

# Tangency with risk free -------------------------------------------------
lambda_t = sqrt((21.613-2)/21.613)*sdP_T6/100
portfolio_var_hat_t = -S*wP_noS*(1/100 + lambda_t*qt(0.05,21.613))  
portfolio_es_hat_t = S*wP_noS*(-1/100 + lambda_t*(
  (dt(qt(0.05,21.613),21.613)/0.05)*((21.613+(qt(0.05,21.613))^2)/(21.613-1))
))

# PCA ---------------------------------------------------------------------
png("Correlation_Matrix.png",width=583,height=486, units = "px") 
par(ps=18)
corrplot(cor(R), method = 'color', tl.col = "black",  addCoef.col = "black",tl.cex=1.1)
dev.off()

pca_returns = princomp(R)
png("PCA.png",width=583,height=486, units = "px") 
cumulative = rep(0,length(unname(pca_returns$sdev^2)))
variances = unname(pca_returns$sdev)^2
percentVariances = unname(pca_returns$sdev^2)/sum(unname(pca_returns$sdev)^2)
for (i in 1:length(unname(pca_returns$sdev^2))){
  cumulative[i] = sum(variances[1:i])/(sum(unname(pca_returns$sdev)^2))
}

pcaDf = data.frame(Component = c(1:length(symbols)), Variance = unname(pca_returns$sdev^2),
                   Cumulative = cumulative, PV = percentVariances)
ggplot(data=pcaDf, aes(x=Component, y=Variance)) +
  geom_bar(stat="identity") +
  ggtitle("Variance vs Principal Component") +
  theme(plot.title = element_text(size = rel(2))) +
  scale_x_discrete(limits = c(1:9)) +
  theme(axis.title.x = element_text(size = rel(1.5))) +
  theme(axis.title.y = element_text(size = rel(1.5))) 
dev.off()

R2 = R
PCn = rep("PC",length(symbols))
for (i in 1:length(symbols)){
  pc = t(pca_returns$loadings[,i]%*%t(R))
  R2 = cbind(R2,pc)
  PCn[i] = paste0("PC",as.character(i))
}
colnames(R2) = c(symbols,PCn)

#Plot all
#png("Correlation_Matrix_w_PC.png",width=583,height=486, units = "px") 
#corrplot(cor(R2), method = 'color', tl.col = "black",  addCoef.col = "black")
#dev.off()

png("Correlation_Matrix_top_Right.png",width=583,height=486, units = "px") 
par(ps=18)
corrplot(cor(R2)[(1:length(symbols)),(length(symbols)+1):(2*length(symbols))], method = 'color',
         tl.col = "black",  addCoef.col = "black", tl.cex=1.1)
dev.off()


# Distribution Fit
library(fGarch)
library(reshape2)
R_full <- as.data.frame(R_full)
R_full <- mutate(R_full, Date = row.names(R_full))
R_full$Date <- as.Date(R_full$Date, format = "%Y-%m-%d")
returnData = R_full[R_full$Date>startDate,-10]
returnDataMelt = melt(returnData,variable.name = "asset",value.name = "returns")

png("Density of Monthly Return.png",width=583,height=486, units = "px") 
returnDensity = ggplot(returnDataMelt, aes(x=returns)) +
  geom_density() +
  facet_wrap(~asset, ncol=3, scales='free') + 
  labs(title = "Density of Monthly Return") + 
  ylab("Density") + 
  xlab("Returns")
returnDensity
dev.off()

criteria = as.data.frame(matrix(0,18,5))
colnames(criteria) = c("t","skewed t","ged","skewed ged","best")
n = dim(returnData)[1]
names = rep(symbols,each = 2)
for(i in 1:length(names)){
  if(i%%2==1){
    names[i] = paste(names[i],"AIC",sep = ".")
  }
  else{
    names[i] = paste(names[i],"BIC",sep = ".")
  }
}
rownames(criteria) = names

for(i in 1:9){
  t = stdFit(returnData[,i])
  AIC = 2*t$objective + 2*length(t$par)
  BIC = 2*t$objective + log(n)*length(t$par)
  criteria[2*i-1,1] = AIC
  criteria[2*i,1] = BIC
  st = sstdFit(returnData[,i])
  AIC = 2*st$minimum + 2*length(st$estimate)
  BIC = 2*st$minimum + log(n)*length(st$estimate)
  criteria[2*i-1,2] = AIC
  criteria[2*i,2] = BIC
  ged = gedFit(returnData[,i])
  AIC = 2*ged$objective + 2*length(ged$par)
  BIC = 2*ged$objective + log(n)*length(ged$par)
  criteria[2*i-1,3] = AIC
  criteria[2*i,3] = BIC
  sged = sgedFit(returnData[,i])
  AIC = 2*sged$objective + 2*length(sged$par)
  BIC = 2*sged$objective + log(n)*length(sged$par)
  criteria[2*i-1,4] = AIC
  criteria[2*i,4] = BIC
  criteria[2*i-1,5] = names(which.min(criteria[2*i-1,]))
  criteria[2*i,5] = names(which.min(criteria[2*i,]))
}
write.csv(criteria,file = "univariate_fit.csv")

# Copula ------------------------------------------------------------------
R_full = read.csv("Portfolio_Monthly_Returns.csv")
emp_R = NULL     # transform the data using the empirials
for(i in 2:ncol(R_full)){
  emp_R = cbind(emp_R, rank(R_full[,i]) / (nrow(R_full) + 1))
}
colnames(emp_R) = colnames(R_full)[2:10]
AIC = NULL

### fit normal copula
png("QQ-plot.png",width=583,height=486, units = "px")
par(mfrow = c(3,3))
for(i in 1:9){
  tmp_z_R = (emp_R[,i] - mean(emp_R[,i]))/sd(emp_R[,i])
  qqnorm(tmp_z_R, main = colnames(emp_R)[i])
  abline(0,1)
}
dev.off()
# QQ-plot shows that the distribution has a lighter tail than normal distribution 

normcop = normalCopula(param = rep(0,36), dim = 9, dispstr = "un")
fnorm = fitCopula(data = emp_R, copula = normcop, method = "mpl")
tmp = -2*fnorm@loglik + 2*fnorm@copula@dimension
AIC = c(AIC, tmp)

### fit t copula
tcop = tCopula(param = rep(0,36), dim = 9, dispstr = "un", df = 10)
ft = fitCopula(data = emp_R, copula = tcop, method = "mpl")
tmp = -2*ft@loglik + 2*ft@copula@dimension
AIC = c(AIC, tmp)

### fit Gumbel copula 
fgumbel = fitCopula(data = emp_R, method="mpl", copula=gumbelCopula(dim=9))
tmp = -2*fgumbel@loglik + 2*fgumbel@copula@dimension
AIC = c(AIC, tmp)

### fit Frank copula
ffrank = fitCopula(data = emp_R, method="mpl", copula=frankCopula(dim=9))
tmp = -2*ffrank@loglik + 2*ffrank@copula@dimension
AIC = c(AIC, tmp)

### fit Clayton copula
fclayton = fitCopula(data = emp_R, method="mpl", copula=claytonCopula(dim=9))
tmp = -2*fclayton@loglik + 2*fclayton@copula@dimension
AIC = c(AIC, tmp)

AIC = data.frame(AIC)
rownames(AIC) = c("normal", "t", "Gumbel", "Frank", "Clayton")
## t-Copula has the minimum AIC, so t distribution fits best

### compare the empirical copula with estimated copulas
### take PG and WMT as example
emp_PW = emp_R[,c(7,9)]
AIC_PW = NULL

### fit normal copula
normcop = normalCopula(param = 0, dim = 2, dispstr = "un")
fnorm_PW = fitCopula(data = emp_PW, copula = normcop, method = "mpl")
tmp = -2*fnorm_PW@loglik + 2*fnorm_PW@copula@dimension
AIC_PW = c(AIC_PW, tmp)

### fit t copula
cor_tau = cor(R_full[,2],R_full[,3], method="kendall")
omega = sin((pi/2) * cor_tau)
tcop = tCopula(omega, dim = 2, dispstr = "un", df = 4)
ft_PW = fitCopula(data = emp_PW, copula = tcop, method = "mpl")
tmp = -2*ft_PW@loglik + 2*ft_PW@copula@dimension
AIC_PW = c(AIC_PW, tmp)

### fit Gumbel copula
fgumbel_PW = fitCopula(data = emp_PW, method="mpl", copula=gumbelCopula(dim=2))
tmp = -2*fgumbel_PW@loglik + 2*fgumbel_PW@copula@dimension
AIC_PW = c(AIC_PW, tmp)

### fit Frank copula 
ffrank_PW = fitCopula(data = emp_PW, method="mpl", copula=frankCopula(dim=2))
tmp = -2*ffrank_PW@loglik + 2*ffrank_PW@copula@dimension
AIC_PW = c(AIC_PW, tmp)

### fit Clayton copula 
fclayton_PW = fitCopula(data = emp_PW, method="mpl", copula=claytonCopula(dim=2))
tmp = -2*fclayton_PW@loglik + 2*fclayton_PW@copula@dimension
AIC_PW = c(AIC_PW, tmp)

AIC_PW = data.frame(AIC_PW)
rownames(AIC_PW) = c("normal", "t", "Gumbel", "Frank", "Clayton")

### plot
dem = pempiricalCopula(emp_PW)
png("Copula.png",width=583,height=486, units = "px")
par(mfrow = c(3,2))
contour(dem$x,dem$y,dem$z,main="Empirical")
contour(normalCopula(fnorm_PW@estimate), pCopula, main="Normal")
contour(tCopula(param=ft_PW@estimate[1]), pCopula,main="t")
contour(gumbelCopula(fgumbel_PW@estimate,dim=2), pCopula, main="Gumbel")
contour(frankCopula(ffrank_PW@estimate, dim=2), pCopula,main="Frank")
contour(claytonCopula(fclayton_PW@estimate, dim=2), pCopula, main="Clayton")
dev.off()

# Times Series Analysis
library(tseries)
library(forecast)
library(hydroTSM)

# data preparation and visualization
SP = getSymbols("^GSPC", from=startDateTest,
                to=stopDate, src="yahoo",auto.assign = FALSE)
SP_df = as.data.frame(SP[,6])
SP_df$date = as.Date(rownames(SP_df))

# monthly return data
SP_monthly_return = monthlyReturn(SP[,6])
SP_mr = as.data.frame(SP_monthly_return)
SP_mr$date = as.Date(rownames(SP_mr))

png("SP500 Return.png",width=583,height=486, units = "px") 
ggplot(SP_mr,aes(date)) + geom_line(aes(y = monthly.returns))+
  labs( title = "S&P 500 Monthly Returns")
dev.off()

# monthly price data
SP_mp = to.monthly(SP)[,6]
SP_mp = as.data.frame(SP_mp)
SP_mp$date = SP_mr$date

png("SP500 Price.png",width=583,height=486, units = "px") 
ggplot(SP_mp,aes(date)) + geom_line(aes(y = SP.Adjusted))+
  labs( title = "S&P 500 Monthly Prices")
dev.off()

# stationary test
png("ACF_re.png",width=583,height=486, units = "px") 
acf(SP_monthly_return)
dev.off()
Box.test(SP_monthly_return) # The monthly return is white noise so we cannot use any model to model the return


SP_mp_ts = ts(SP_mp$SP.Adjusted,start = c(2009,11),frequency = 12)
png("ACF_pr.png",width=583,height=486, units = "px") 
acf(SP_mp_ts)
dev.off()
Box.test(SP_mp_ts)

# use arima to model the price
auto.arima(SP_mp_ts)
fit = arima(SP_mp_ts,order=c(1,1,0))
forecasts = predict(fit,3)

# decomposition
SP_mr_ts = ts(SP_mr$monthly.returns,frequency=12,start = c(2009,11))
SP_r_de = decompose(SP_mr_ts)

png("Decompsition_re.png",width=583,height=486, units = "px") 
plot(SP_r_de)
dev.off()

SP_de = decompose(SP_mp_ts)
png("Decompsition_pr.png",width=583,height=486, units = "px") 
plot(SP_de)
dev.off()

# Descriptive -------------------------------------------------------------

# Read in Risk Free Data: Treasury bills (secondary market): 4-week
riskFree = read.csv('FRB_H15.csv',
                    stringsAsFactors=FALSE)
riskFree = riskFree[c(-5:-1),] # remove header information
riskFree[,1] = as.Date(riskFree[,1])
startDateTest = "2009-11-02"
startDate = "2010-11-01"
stopDate = "2015-11-26"
startIX = which(riskFree[,1] == startDateTest)  
stopIX = which(riskFree[,1] == stopDate)  
riskFree = riskFree[c(startIX:stopIX),] #set date range
riskFree[,2] = as.double(riskFree[,2])

# Get Stock Market Data ---------------------------------------------------
#Berkshire Hathaway Large Investments
symbols = c("AXP","IBM","KO","MCO","WFC","DVA","PG","USB","WMT")

#use S&P500 for market portfolio for CAPM
marketP = getSymbols("^GSPC", from=startDateTest, to=stopDate, src="yahoo",auto.assign = FALSE) 
marketP2 = as.numeric(monthlyReturn(marketP[,6]))
n = length(marketP2)[1] 

mufreeV_full = array(0,c(n)) # 0% interest
RM = 100*marketP2 # monthly market return in percent 
#100*(marketP2[2:n]/marketP2[1:(n-1)] - 1)  #Average daily market returns in percent
marketIX = index(marketP[c(-1,-1*(n+1)),])
for (i in 1:length(mufreeV_full)){ # get risk free daily returns and align with the asset data 
  ix = which(riskFree[,1] == marketIX[i])
  if (is.na(riskFree[i,2])){ # if there is no rate, substitute the rate from the day before
    riskFree[i,2] = riskFree[i-1,2]
  }
  mufreeV_full[i] = riskFree[i,2]/12 #monthly risk free return
}

# If the applicable returns have been saved off, load the file, if not, scrape the whole
# list from yahoo finance and save it off
get_data <- function(symbols, startDateTest, stopDate){
  
  R_full = try(read.csv("Portfolio_Monthly_Returns.csv"))
  
  if (typeof(R_full) != "character"){
    R_full2 <- R_full[,-1]
    rownames(R_full2) <- R_full[,1]
    return(R_full2)
  }
  else{
    assign(symbols[1], getSymbols(symbols[1], from=startDateTest, to=stopDate,
                                  src="yahoo",auto.assign = FALSE))
    
    R_full = cbind(monthlyReturn(get(symbols[1])[,6]))
    
    for (symbol in symbols[2:length(symbols)]){
      assign(symbol, 
             getSymbols(symbol, from=startDateTest, to = stopDate, src="yahoo",auto.assign = FALSE))
      assign(paste0(symbol,".a"), 
             adjustOHLC(get(symbol), symbol.name=symbol))
      assign(paste0(symbol,".uA"), 
             adjustOHLC(get(symbol), symbol.name=symbol, use.Adjusted=TRUE)) #get(symbol, pos=.GlobalEnv)
      R_full = cbind(R_full,monthlyReturn(get(paste0(symbol,".uA"))[,6]))
    }
    colnames(R_full) <- symbols
    write.csv(as.data.frame(R_full),"Portfolio_Monthly_Returns.csv",
              row.names = TRUE)
    return(R_full)
  }
}

R_full = get_data(symbols, startDateTest, stopDate) 
means = apply(R_full,2,mean)

# Analysis ----------------------------------------------------------------
library(psych)
# means, standard deviations, skewness coefficients, kurtosis coefficients
describe(R_full)

# monthly prices and returns
library(dplyr)
library(zoo)
library(reshape2)
stockP <- getSymbols(symbols[1], from=startDate, to=stopDate, src="yahoo",auto.assign = FALSE) # create a blank dataset collecting stock prices
stockP <- to.monthly(stockP)
stockP <- as.data.frame(stockP)
stockP <- mutate(stockP, Date = row.names(stockP))
stockP <- select(stockP, Date)
for (symbol in symbols[1:9]){ #Retreive stock prices and populate them into the blank dataset
  stockP_temp <- assign(symbol, getSymbols(symbol, from=startDateTest, to=stopDate, src="yahoo",auto.assign = FALSE))
  stockP_temp <- to.monthly(stockP_temp)
  stockP_temp <- as.data.frame(stockP_temp)
  stockP_temp <- mutate(stockP_temp, Date = row.names(stockP_temp))
  stockP_temp <- select(stockP_temp, Date, ends_with("Adjusted"))
  colnames(stockP_temp) <- c("Date", symbol)
  stockP <- merge(stockP, stockP_temp)
}
stockP$Date <- as.Date(as.yearmon(stockP$Date, format = "%b %Y"))
stockP <- as.data.frame(stockP)
dat.melt.P <- melt(stockP, id.vars='Date')


R_full <- as.data.frame(R_full)
R_full <- mutate(R_full, Date = row.names(R_full))
R_full$Date <- as.Date(R_full$Date, format = "%Y-%m-%d")
dat.melt <- melt(R_full, id.vars='Date')

# plot monthly returns
P_return <- ggplot(dat.melt, aes(x=Date, y=value)) +
  geom_line() +
  facet_wrap(~variable, ncol=3, scales='free') + 
  labs(title = "Monthly Return") + 
  ylab("Monthly Return")
print(P_return)

# plot monthly prices
P_price <- ggplot(dat.melt.P, aes(x=Date, y=value)) +
  geom_line() +
  facet_wrap(~variable, ncol=3, scales='free') + 
  labs(title = "Monthly Price") + 
  ylab("Monthly Price")
print(P_price)

# equity curve for each asset and S&P500
stockOrder = stockP[order(stockP$Date),]
for (col in 2:dim(stockOrder)[2]){
  base <- stockOrder[1, col]
  for (row in 1:dim(stockOrder)[1]){
    stockOrder[row, col] <- stockOrder[row, col] / base
  }
}

dat.melt.df = melt(stockOrder, id.vars='Date')
P_df <- ggplot(dat.melt.df, aes(x=Date, y=value)) +
  geom_line() +
  facet_wrap(~variable, ncol=3, scales='free') + 
  labs(title = "Equity Curve") + 
  ylab("Dollars")
print(P_df)


# histograms, boxplots and qq-plots for each return series
##histograms
P_hist <- ggplot(dat.melt, aes(x=value)) +
  geom_histogram() +
  facet_wrap(~variable, ncol=3, scales='free')
print(P_hist)

##boxplot
P_box <- ggplot(dat.melt, aes(x = Date, y= value)) +
  geom_boxplot() +
  facet_wrap(~variable, ncol=3, scales='free')
print(P_box)

##qqplot
ggplot(dat.melt, aes(sample = value)) + stat_qq() + facet_wrap(~ variable, ncol=3)

# test for stationarity
library(tseries)
adf.test(R_full$AXP)
adf.test(R_full$IBM)
adf.test(R_full$DVA)
adf.test(R_full$KO)
adf.test(R_full$PG)
adf.test(R_full$USB)
adf.test(R_full$MCO)
adf.test(R_full$WFC)
adf.test(R_full$WMT)

# pairwise scatterplot
#pairs(cbind(AXP,IBM,KO,MCO,WFC,DVA,PG,USB,WMT))
pairs(R_full)

# sample covariance matrix of returns on assets
R_full_withnodate <- select(R_full, -Date)
cov_mat = cov(R_full_withnodate)
cov_mat

