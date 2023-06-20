import React from "react";
import {BrowserRouter, Route, Routes} from "react-router-dom";
import NavBar from "./components/NavBar";
import Footer from "./components/Footer";
import Box from "@mui/material/Box";

function App() {
    return (
        <>
            <NavBar/>
            <Box sx={{height: '3000px', backgroundColor:'red'}}></Box>
            <BrowserRouter>
                <Routes>
                    <Route exact path="/" element={<HomePage />} />
                    <Route path="/create" element={<AddEntry />} />
                </Routes>
            </BrowserRouter>
            <Footer/>
        </>
    );
}

export default App;
